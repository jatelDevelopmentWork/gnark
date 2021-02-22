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

	bn256witness "github.com/consensys/gnark/internal/backend/bn256/witness"
	"github.com/consensys/gurvy/bn256/fr"
)

// VerifyRaw verifies a PLONK proof
// TODO use Fiat Shamir to derive the challenges
func VerifyRaw(proof *Proof, publicData *PublicRaw, publicWitness bn256witness.Witness) bool {

	// step 1: verify that qlL+qrR+qmL.R+qoO+k=Z*H, by evaluating the LHS at the challenge zeta
	var zeta fr.Element
	zeta.SetString("2938092839238274283")

	var ql, qr, qm, qo, qk, tmp fr.Element
	_ql := publicData.Ql.Eval(&zeta)
	_qr := publicData.Qr.Eval(&zeta)
	_qm := publicData.Qm.Eval(&zeta)
	_qo := publicData.Qo.Eval(&zeta)
	_qk := publicData.Qk.Eval(&zeta)
	ql.Set(_ql.(*fr.Element))
	qr.Set(_qr.(*fr.Element))
	qm.Set(_qm.(*fr.Element))
	qo.Set(_qo.(*fr.Element))
	qk.Set(_qk.(*fr.Element))

	var lhs, rhs, one fr.Element
	lhs.Mul(&ql, &proof.ClaimedValues[0])
	tmp.Mul(&qr, &proof.ClaimedValues[1])
	lhs.Add(&lhs, &tmp)
	tmp.Mul(&qm, &proof.ClaimedValues[0]).Mul(&tmp, &proof.ClaimedValues[1])
	lhs.Add(&lhs, &tmp)
	tmp.Mul(&qo, &proof.ClaimedValues[2])
	lhs.Add(&lhs, &tmp).Add(&lhs, &qk)
	var bc big.Int
	one.SetOne()
	bc.SetUint64(publicData.DomainNum.Cardinality)
	rhs.Exp(zeta, &bc).Sub(&rhs, &one).Mul(&rhs, &proof.ClaimedValues[3])

	if !lhs.Equal(&rhs) {
		return false
	}

	return true

	// following steps WIP

}
