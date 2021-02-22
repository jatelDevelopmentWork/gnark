// Copyright 2020 ConsenSys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package plonk

import (
	"math/big"

	"github.com/consensys/gnark/crypto/polynomial"
	"github.com/consensys/gnark/crypto/polynomial/bn256"
	"github.com/consensys/gnark/internal/backend/bn256/cs"
	"github.com/consensys/gnark/internal/backend/bn256/fft"
	bn256witness "github.com/consensys/gnark/internal/backend/bn256/witness"
	"github.com/consensys/gurvy/bn256/fr"
)

// Proof PLONK proofs, consisting of opening proofs
type Proof struct {

	// Claimed Values are the values of L,R,O,H at zeta (wip for the remaining values)
	ClaimedValues [4]fr.Element

	// batch opening proofs for L,R,O,H at zeta
	BatchOpenings polynomial.BatchOpeningProofSinglePoint
}

// comute the solution l, r, o, and returns it in canonical form.
func computeLRO(spr *cs.SparseR1CS, publicData *PublicRaw, witness bn256witness.Witness) (bn256.Poly, bn256.Poly, bn256.Poly) {

	solution, _ := spr.Solve(witness)

	s := publicData.DomainNum.Cardinality

	var l, r, o bn256.Poly
	l = make([]fr.Element, s)
	r = make([]fr.Element, s)
	o = make([]fr.Element, s)

	for i := 0; i < len(spr.Constraints); i++ {
		l[i].Set(&solution[spr.Constraints[i].L.VariableID()])
		r[i].Set(&solution[spr.Constraints[i].R.VariableID()])
		o[i].Set(&solution[spr.Constraints[i].O.VariableID()])
	}
	offset := len(spr.Constraints)
	for i := 0; i < len(spr.Assertions); i++ {
		l[offset+i].Set(&solution[spr.Assertions[i].L.VariableID()])
		r[offset+i].Set(&solution[spr.Assertions[i].R.VariableID()])
		o[offset+i].Set(&solution[spr.Assertions[i].O.VariableID()])
	}

	publicData.DomainNum.FFTInverse(l, fft.DIF, 0)
	publicData.DomainNum.FFTInverse(r, fft.DIF, 0)
	publicData.DomainNum.FFTInverse(o, fft.DIF, 0)
	fft.BitReverse(l)
	fft.BitReverse(r)
	fft.BitReverse(o)

	return l, r, o

}

// evaluate evaluates a polynomial of degree m=domainNum.Cardinality on the 2 cosets
// 1 and 3 of (Z/4mZ)/(Z/mZ), so it dodges Z/mZ (+Z/2mZ), the vanishing set of Z.
//
// Puts the result in res (of size 2*domain.Cardinality).
//
// Both sizes of poly and res are powers of 2, len(res) = 2*len(poly).
func evaluate(poly, res []fr.Element, domain *fft.Domain) {

	// build a copy of poly padded with 0 so it has the length of the closest power of 2 of poly
	evaluations := make([][]fr.Element, 2)
	evaluations[0] = make([]fr.Element, domain.Cardinality)
	evaluations[1] = make([]fr.Element, domain.Cardinality)

	// evaluations[i] must contain poly in the canonical basis
	copy(evaluations[0], poly)
	copy(evaluations[1], evaluations[0])

	domain.FFT(evaluations[0], fft.DIF, 1)
	domain.FFT(evaluations[1], fft.DIF, 3)
	fft.BitReverse(evaluations[0])
	fft.BitReverse(evaluations[1])

	//res := make([]fr.Element, 2*domain.Cardinality)
	for i := uint64(0); i < domain.Cardinality; i++ {
		res[2*i].Set(&evaluations[0][i])
		res[2*i+1].Set(&evaluations[1][i])
	}
}

// computeNumFirstClaim computes the evaluation of lL+qrR+qqmL.R+qoO+k on
// the coset 1 of (Z/4mZ)/(Z/2mZ), where m=nbConstraints+nbAssertions.
//
// qlL+qrR+qmL.R+qoO+k = H*Z, where Z=x^n-1
//
// l, r, o must be of size 2^n.
func computeNumFirstClaim(publicData *PublicRaw, l, r, o []fr.Element) []fr.Element {

	// data
	evalL := make([]fr.Element, 2*publicData.DomainNum.Cardinality)
	evalR := make([]fr.Element, 2*publicData.DomainNum.Cardinality)
	evalO := make([]fr.Element, 2*publicData.DomainNum.Cardinality)

	evalQl := make([]fr.Element, 2*publicData.DomainNum.Cardinality)
	evalQr := make([]fr.Element, 2*publicData.DomainNum.Cardinality)
	evalQm := make([]fr.Element, 2*publicData.DomainNum.Cardinality)
	evalQo := make([]fr.Element, 2*publicData.DomainNum.Cardinality)
	evalQk := make([]fr.Element, 2*publicData.DomainNum.Cardinality)

	// public vectors
	evaluate(publicData.Ql, evalQl, publicData.DomainNum)
	evaluate(publicData.Qr, evalQr, publicData.DomainNum)
	evaluate(publicData.Qm, evalQm, publicData.DomainNum)
	evaluate(publicData.Qo, evalQo, publicData.DomainNum)
	evaluate(publicData.Qk, evalQk, publicData.DomainNum)

	// solution vectors
	evaluate(l, evalL, publicData.DomainNum)
	evaluate(r, evalR, publicData.DomainNum)
	evaluate(o, evalO, publicData.DomainNum)

	// computes the evaluation of qrR+qlL+qmL.R+qoO+k on the coset
	// 1 of (Z/4mZ)/(Z/2mZ)
	var acc, buf fr.Element
	for i := uint64(0); i < 2*publicData.DomainNum.Cardinality; i++ {

		acc.Mul(&evalQl[i], &evalL[i]) // ql.l

		buf.Mul(&evalQr[i], &evalR[i])
		acc.Add(&acc, &buf) // ql.l + qr.r

		buf.Mul(&evalQm[i], &evalL[i]).Mul(&buf, &evalR[i])
		acc.Add(&acc, &buf) // ql.l + qr.r + qm.l.r

		buf.Mul(&evalQo[i], &evalO[i])
		acc.Add(&acc, &buf)            // ql.l + qr.r + qm.l.r + qo.o
		evalL[i].Add(&acc, &evalQk[i]) // ql.l + qr.r + qm.l.r + qo.o + k
	}

	return evalL
}

// computeH computes h = num/Z, where:
// * Z = X^m-1, m=2^n
// * num (of size 2^{n+1}) is the evaluation of a polynomial of
// 	degree 3*m on 2m=2^{n+1} points (coset 1 of (Z/2mZ)/(Z/mZ)).
// The result is h in the canonical basis.
func computeH(num bn256.Poly, publicData *PublicRaw) bn256.Poly {

	h := make([]fr.Element, publicData.DomainH.Cardinality)

	// evaluate Z
	var one fr.Element
	var expo big.Int
	expo.SetUint64(publicData.DomainNum.Cardinality)
	zPoly := make([]fr.Element, 2)
	one.SetOne()
	zPoly[0].Exp(publicData.DomainNum.FinerGenerator, &expo) // finerGen**DomainNum.Cardinality
	zPoly[1].Square(&zPoly[0]).Mul(&zPoly[1], &zPoly[0])     // (finerGen**3)**DomainNum.Cardinality
	zPoly[0].Sub(&zPoly[0], &one)
	zPoly[1].Sub(&zPoly[1], &one)

	// h = num/Z
	for i := 0; i < int(publicData.DomainH.Cardinality); i++ {
		h[i].Div(&num[i], &zPoly[i%2])
	}

	// express h in the canonical basis
	publicData.DomainH.FFTInverse(h, fft.DIF, 1)
	fft.BitReverse(h)

	return h
}

// Prove from the public data representing a circuit, and the solution
// l, r, o, outputs a proof that the assignment is valid.
//
// It computes H such that qlL+qrR+qmL.R+qoO+k = H*Z, Z = X^m-1
// TODO add a parameter to force the resolution of the system even if a constraint does not hold, so we can cleanly check that the prover fails
func Prove(spr *cs.SparseR1CS, publicData *PublicRaw, witness bn256witness.Witness) *Proof {

	// evaluate qlL+qrR+qmL.R+qoO+k on 2*m points
	l, r, o := computeLRO(spr, publicData, witness)
	num := computeNumFirstClaim(publicData, l, r, o)

	// TODO wip, compute the remaining part of the num

	// compute h (its evaluation)
	h := computeH(num, publicData)

	// compute challenge
	// TODO use fiat Shamir to sample zeta and challenge
	var zeta, challenge fr.Element
	zeta.SetString("2938092839238274283")
	challenge.SetString("987545678")

	proof := &Proof{}
	tmp := l.Eval(&zeta)
	proof.ClaimedValues[0].Set(tmp.(*fr.Element))
	tmp = r.Eval(&zeta)
	proof.ClaimedValues[1].Set(tmp.(*fr.Element))
	tmp = o.Eval(&zeta)
	proof.ClaimedValues[2].Set(tmp.(*fr.Element))
	tmp = h.Eval(&zeta)
	proof.ClaimedValues[3].Set(tmp.(*fr.Element))

	proof.BatchOpenings = publicData.CommitmentScheme.BatchOpenSinglePoint(&zeta, &challenge, l, r, o, h)

	return proof
}
