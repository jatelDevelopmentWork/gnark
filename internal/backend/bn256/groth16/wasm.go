package groth16

const wasmTemplate = `
#include <array>
#include "platon/platon.hpp"
using namespace platon;

const std::uint256_t PRIME_Q = "21888242871839275222246405745257275088696311157297823662689037894645226208583"_uint256;
const std::uint256_t SNARK_SCALAR_FIELD = "21888242871839275222246405745257275088548364400416034343698204186575808495617"_uint256;

CONTRACT Verify : public platon::Contract{
private:
	struct G1Point{
		std::uint256_t X;
		std::uint256_t Y;
	};

	// Encoding of field elements is: X[0] * z + X[1]
	struct G2Point{
		std::array<std::uint256_t, 2> X;
		std::array<std::uint256_t, 2> Y;
	};

private:
	// return The negation of p, i.e. p.plus(p.negate()) should be zero.
	G1Point negate(const G1Point &p){
		if (p.X == 0 && p.Y == 0)
		{
			return G1Point{0, 0};
		}

		return G1Point{p.X, PRIME_Q - (p.Y % PRIME_Q)};
	}

	// return The sum of two points of G1
	G1Point plus(const G1Point &p1, const G1Point &p2){
		G1Point temp;
		bn256_g1_add(p1.X.Values(), p1.Y.Values(), p2.X.Values(), p2.Y.Values(), temp.X.Values(), temp.Y.Values());
		return temp;
	}

	/*
   * @return The product of a point on G1 and a scalar, i.e.
   * p == p.scalar_mul(1) and p.plus(p) == p.scalar_mul(2) for all
   * points p.
   */
	G1Point scalar_mul(const G1Point &p1, const std::uint256_t &s){
		G1Point temp;
		bn256_g1_mul(p1.X.Values(), p1.Y.Values(), s.Values(), temp.X.Values(), temp.Y.Values());
		return temp;
	}

	/* @return The result of computing the pairing check
   * e(p1[0], p2[0]) *  .... * e(p1[n], p2[n]) == 1
   * For example,
   * pairing([P1(), P1().negate()], [P2(), P2()]) should return true.
   */
	bool pairing(const G1Point &a1, const G2Point &a2, const G1Point &b1,
				 const G2Point &b2, const G1Point &c1, const G2Point &c2,
				 const G1Point &d1, const G2Point &d2){
		G1Point p1[4] = {a1, b1, c1, d1};
		G2Point p2[4] = {a2, b2, c2, d2};

		size_t len = sizeof(p1) / sizeof(p1[0]);
		size_t size = sizeof(uint8_t *) * len;
		uint8_t **x1 = (uint8_t **)malloc(size);
		uint8_t **y1 = (uint8_t **)malloc(size);
		uint8_t **x11 = (uint8_t **)malloc(size);
		uint8_t **y11 = (uint8_t **)malloc(size);
		uint8_t **x12 = (uint8_t **)malloc(size);
		uint8_t **y12 = (uint8_t **)malloc(size);

		for (size_t i = 0; i < len; i++){
			x1[i] = p1[i].X.Values();
			y1[i] = p1[i].Y.Values();
			x11[i] = p2[i].X[0].Values();
			y11[i] = p2[i].Y[0].Values();
			x12[i] = p2[i].X[1].Values();
			y12[i] = p2[i].Y[1].Values();
		}

		return 0 == bn256_pairing(x1, y1, x11, x12, y11, y12, len);
	}

private:
	struct VerifyingKey{
		G1Point alfa1;
		G2Point beta2;
		G2Point gamma2;
		G2Point delta2;
		std::array<G1Point, {{len .G1.K}}> IC;
	};

	struct Proof{
		G1Point A;
		G2Point B;
		G1Point C;
	};

	// 获取 vk 的值
	VerifyingKey get_verifyingKey(){
		VerifyingKey vk;

		vk.alfa1 = G1Point{"{{.G1.Alpha.X.String}}"_uint256, "{{.G1.Alpha.Y.String}}"_uint256};
		vk.beta2 = G2Point{ {"{{.G2.Beta.X.A1.String}}"_uint256, "{{.G2.Beta.X.A0.String}}"_uint256}, {"{{.G2.Beta.Y.A1.String}}"_uint256, "{{.G2.Beta.Y.A0.String}}"_uint256} };
		vk.gamma2 = G2Point{ {"{{.G2.Gamma.X.A1.String}}"_uint256, "{{.G2.Gamma.X.A0.String}}"_uint256}, {"{{.G2.Gamma.Y.A1.String}}"_uint256, "{{.G2.Gamma.Y.A0.String}}"_uint256} };
		vk.delta2 = G2Point{ {"{{.G2.Delta.X.A1.String}}"_uint256, "{{.G2.Delta.X.A0.String}}"_uint256}, {"{{.G2.Delta.Y.A1.String}}"_uint256, "{{.G2.Delta.Y.A0.String}}"_uint256} };
		{{- range $i, $ki := .G1.K }}   
		vk.IC[{{$i}}] = G1Point{ "{{$ki.X.String}}"_uint256, "{{$ki.Y.String}}"_uint256};
		{{- end}}

		return vk;
	}

public:
	CONST void init() {}

	using Array2Uint256 = std::array<std::uint256_t, 2>;
	CONST bool verify_proof(Array2Uint256 a, std::array<Array2Uint256, 2> b, Array2Uint256 c, std::array<std::uint256_t, {{len .G1.K | sub 1}}> input){
		Proof proof{G1Point{a[0], a[1]}, G2Point{ {b[0][0], b[0][1]}, {b[1][0], b[1][1]} }, G1Point{c[0], c[1]}};
		VerifyingKey vk = get_verifyingKey();

		// Compute the linear combination vk_x
		G1Point vk_x = G1Point{0, 0};

		// Make sure that proof.A, B, and C are each less than the prime q
		if (proof.A.X > PRIME_Q) platon_revert();
		if (proof.A.Y > PRIME_Q) platon_revert();
		if (proof.B.X[0] > PRIME_Q) platon_revert();
		if (proof.B.Y[0] > PRIME_Q) platon_revert();
		if (proof.B.X[1] > PRIME_Q) platon_revert();
		if (proof.B.Y[1] > PRIME_Q) platon_revert();
		if (proof.C.X > PRIME_Q) platon_revert();
		if (proof.C.Y > PRIME_Q) platon_revert();

		// Make sure that every input is less than the snark scalar field
		int length = input.size();
		for (int i = 0; i < length; i++){
			if (input[i] > SNARK_SCALAR_FIELD)
				platon_revert();
			vk_x = plus(vk_x, scalar_mul(vk.IC[i + 1], input[i]));
		}
		vk_x = plus(vk_x, vk.IC[0]);

		// result
		return pairing(negate(proof.A), proof.B, vk.alfa1, vk.beta2, vk_x,
					   vk.gamma2, proof.C, vk.delta2);
	}
};

PLATON_DISPATCH(Verify, (init)(verify_proof))
`
