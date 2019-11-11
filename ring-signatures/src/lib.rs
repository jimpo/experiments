mod matrix;
mod util;

use crate::matrix::{MatrixMN, MatrixNN};
use crate::util::ScalarPowersIterator;

use curve25519_dalek::{
	ristretto::RistrettoPoint,
	scalar::Scalar,
	traits::{MultiscalarMul, VartimeMultiscalarMul},
};
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::iter;
use curve25519_dalek::traits::IsIdentity;

pub struct PublicParams {
	pub label: &'static [u8],
	pub g: RistrettoPoint,
	pub h: RistrettoPoint,
}

#[derive(Debug)]
pub enum ProofError {
	IndexOutOfRange,
	RingIsEmpty,
	RingTooLarge,
}

#[derive(Debug)]
pub enum VerifyError {
	RingIsEmpty,
	RingTooLarge,
}

pub struct Proof {
	c_l: Vec<RistrettoPoint>,
	c_a: Vec<RistrettoPoint>,
	c_b: Vec<RistrettoPoint>,
	c_d: Vec<RistrettoPoint>,
	f: Vec<Scalar>,
	z_a: Vec<Scalar>,
	z_b: Vec<Scalar>,
	z_d: Scalar,
}

/// Proves that the signer has knowledge of the opening of at least one Pedersen commitment
/// to 0 in a vector.
///
/// :param: c a vector of Pedersen commitments
/// :param: idx index into c of the commitment to 0 with known opening
/// :param: key the blinding factor of the idx'th commitment
pub fn prove<R>(
	params: &PublicParams,
	rng: &mut R,
	pubkeys: &[RistrettoPoint],
	idx: u32,
	key: Scalar
) -> Result<Proof, ProofError>
	where R: RngCore + CryptoRng
{
	let len = u32::try_from(pubkeys.len())
		.map_err(|_| ProofError::RingTooLarge)?;
	if len == 0 {
		return Err(ProofError::RingIsEmpty);
	}
	if idx >= len {
		return Err(ProofError::IndexOutOfRange);
	}

	let mut transcript = Transcript::new(params.label);
	transcript.append_u64(b"RING LEN", len as u64);
	transcript.append_message(b"RING", &serialize_points(pubkeys));

	let mut rng = transcript
		.build_rng()
		.rekey_with_witness_bytes(b"KEY", key.as_bytes())
		.finalize(rng);

	let (c, n, log_n) = pad_ring(pubkeys);

	// Bit decomposition of index idx in little-endian order.
	let l = (0..log_n)
		.map(|j| Scalar::from((idx >> j) & 1))
		.collect::<Vec<_>>();

	let r = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let a = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let s = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let t = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let rho = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();

	let c_l = l.iter().zip(r.iter())
		.map(|(l_j, r_j)| pedersen_commit(params, l_j, r_j))
		.collect::<Vec<_>>();
	let c_a = a.iter().zip(s.iter())
		.map(|(a_j, s_j)| pedersen_commit(params, a_j, s_j))
		.collect::<Vec<_>>();
	let c_b = a.iter().zip(l.iter()).zip(t.iter())
		.map(|((a_j, l_j), t_j)| pedersen_commit(params, &(a_j * l_j), t_j))
		.collect::<Vec<_>>();

	let p = compute_p_coefficients(n, log_n, idx, &a);

	let c_d = (0..log_n as usize)
		.map(|k| {
			let (scalars, points): (Vec<&Scalar>, Vec<&RistrettoPoint>) = (0..n as usize)
				.map(|i| (&p[(i, k)], c[i]))
				.chain(iter::once((&rho[k], &params.g)))
				.unzip();
			RistrettoPoint::multiscalar_mul(scalars, points)
		})
		.collect::<Vec<_>>();

	transcript.append_message(b"c_l", &serialize_points(&c_l));
	transcript.append_message(b"c_a", &serialize_points(&c_a));
	transcript.append_message(b"c_b", &serialize_points(&c_b));
	transcript.append_message(b"c_d", &serialize_points(&c_d));

	let x = challenge_scalar(&mut transcript, b"x");

	let x_powers = ScalarPowersIterator::new(x)
		.take(log_n as usize + 1)
		.collect::<Vec<_>>();

	let f = l.iter().zip(a.iter())
		.map(|(l_j, a_j)| l_j * x + a_j)
		.collect::<Vec<_>>();
	let z_a = r.iter().zip(s.iter())
		.map(|(r_j, s_j)| r_j * x + s_j)
		.collect::<Vec<_>>();
	let z_b = r.iter().zip(f.iter()).zip(t.iter())
		.map(|((r_j, f_j), t_j)| r_j * (x - f_j) + t_j)
		.collect::<Vec<_>>();
	let z_d = inner_product(
		rho.iter()
			.map(|rho_k| -rho_k)
			.chain(iter::once(key)),
		x_powers.iter()
	);

	Ok(Proof {
		c_l,
		c_a,
		c_b,
		c_d,
		f,
		z_a,
		z_b,
		z_d,
	})
}

struct VerifyCondition {
	g_scalar: Scalar,
	h_scalar: Scalar,
	scalars: Vec<Scalar>,
	points: Vec<RistrettoPoint>,
}

impl VerifyCondition {
	fn scale(self, x: Scalar) -> VerifyCondition {
		VerifyCondition {
			g_scalar: self.g_scalar * x,
			h_scalar: self.h_scalar * x,
			scalars: self.scalars.into_iter()
				.map(|scalar| scalar * x)
				.collect(),
			points: self.points,
		}
	}

	fn combine(self, other: VerifyCondition) -> VerifyCondition {
		VerifyCondition {
			g_scalar: self.g_scalar + other.g_scalar,
			h_scalar: self.h_scalar + other.h_scalar,
			scalars: self.scalars.into_iter()
				.chain(other.scalars.into_iter())
				.collect(),
			points: self.points.into_iter()
				.chain(other.points.into_iter())
				.collect(),
		}
	}

	fn verify(&self, params: &PublicParams) -> bool {
		RistrettoPoint::vartime_multiscalar_mul(
			self.scalars.iter().chain(vec![&self.g_scalar, &self.h_scalar].into_iter()),
			self.points.iter().chain(vec![&params.g, &params.h].into_iter()),
		).is_identity()
	}

	fn verify_many<R, I>(params: &PublicParams, rng: &mut R, conditions: I) -> bool
		where
			R: RngCore + CryptoRng,
			I: IntoIterator<Item=Self>,
	{
		let mut conditions_iter = conditions.into_iter();
		let first_condition = match conditions_iter.next() {
			Some(condition) => condition,
			None => return false,
		};

		conditions_iter
			.fold(first_condition, |combined, condition| {
				combined.combine(condition.scale(Scalar::random(rng)))
			})
			.verify(params)
	}
}

/// :param: c a vector of Pedersen commitments
/// :param: pi a proof tuple
pub fn verify<R>(
	params: &PublicParams,
	rng: &mut R,
	pubkeys: &[RistrettoPoint],
	proof: &Proof,
) -> Result<bool, VerifyError>
	where
		R: RngCore + CryptoRng,
{
	let len = u32::try_from(pubkeys.len())
		.map_err(|_| VerifyError::RingTooLarge)?;
	if len == 0 {
		return Err(VerifyError::RingIsEmpty);
	}

	let mut transcript = Transcript::new(params.label);
	transcript.append_u64(b"RING LEN", len as u64);
	transcript.append_message(b"RING", &serialize_points(pubkeys));

	let (c, n, log_n) = pad_ring(pubkeys);

	let Proof {
		c_l,
		c_a,
		c_b,
		c_d,
		f,
		z_a,
		z_b,
		z_d,
	} = proof;

	transcript.append_message(b"c_l", &serialize_points(&c_l));
	transcript.append_message(b"c_a", &serialize_points(&c_a));
	transcript.append_message(b"c_b", &serialize_points(&c_b));
	transcript.append_message(b"c_d", &serialize_points(&c_d));

	let x = challenge_scalar(&mut transcript, b"x");

	let mut conditions = Vec::with_capacity(2 * log_n as usize + 1);
	for j in 0..(log_n as usize) {
		conditions.push(VerifyCondition {
			g_scalar: -z_a[j],
			h_scalar: -f[j],
			scalars: vec![x, Scalar::one()],
			points: vec![c_l[j], c_a[j]],
		});
		conditions.push(VerifyCondition {
			g_scalar: -z_b[j],
			h_scalar: Scalar::zero(),
			scalars: vec![x - f[j], Scalar::one()],
			points: vec![c_l[j], c_b[j]],
		});
	}

	let c_exp = (0..n as usize)
		.map(|i| {
			(0..log_n as usize)
				.map(|j| {
					let i_j = (i >> j) & 1;
					if i_j == 0 {
						x - f[j]
					} else {
						f[j]
					}
				})
				.fold(Scalar::one(), |prod, f_ij| prod * f_ij)
		});
	let c_d_exp = ScalarPowersIterator::new(x)
		.take(log_n as usize)
		.map(|x_j| -x_j)
		.collect::<Vec<_>>();

	conditions.push(VerifyCondition {
		g_scalar: -z_d,
		h_scalar: Scalar::zero(),
		scalars: c_exp.chain(c_d_exp.into_iter()).collect(),
		points: c.into_iter().chain(c_d.into_iter()).cloned().collect(),
	});

	Ok(VerifyCondition::verify_many(params, rng, conditions))
}

fn serialize_points(c: &[RistrettoPoint]) -> Vec<u8> {
	let mut output = Vec::with_capacity(32 * c.len());
	for c_i in c.iter() {
		output.extend_from_slice(c_i.compress().as_bytes());
	}
	output
}

// Precondition: length of ring is in (0, 2^32).
fn pad_ring(pubkeys: &[RistrettoPoint]) -> (Vec<&RistrettoPoint>, u32, u32) {
	let len = pubkeys.len() as u32;

	// len is in (0, 2^32), so leading_zeros must be strictly less than 32.
	let log_n = 32 - (len - 1).leading_zeros();
	let n = 1 << log_n;
	let c = pubkeys.iter()
		.chain(pubkeys.iter())
		.take(n as usize)
		.collect();
	(c, n, log_n)
}

fn pedersen_commit(params: &PublicParams, x: &Scalar, r: &Scalar) -> RistrettoPoint {
	RistrettoPoint::multiscalar_mul(vec![x, r], vec![params.h, params.g])
}

pub fn compute_p_coefficients(n: u32, log_n: u32, idx: u32, a: &[Scalar]) -> MatrixMN {
	let x = (1..=log_n)
		.map(Scalar::from)
		.collect::<Vec<_>>();
	let x_powers_mat = MatrixNN::vandermonde(&x);
	let x_log_n_powers = (0..log_n as usize)
		.map(|i| x_powers_mat[(i, log_n as usize - 1)] * x[i])
		.collect::<Vec<_>>();

	let mut a_mat = MatrixNN::zeros(log_n as usize);
	let mut x_mat = MatrixNN::zeros(log_n as usize);
	for i in 0..(log_n as usize) {
		for j in 0..(log_n as usize) {
			a_mat[(i, j)] = a[j as usize];
			x_mat[(i, j)] = x[i as usize];
		}
	}

	let f = [
		[-(&a_mat), a_mat.clone()],
		[&x_mat - &a_mat, &x_mat + &a_mat],
	];

	// Evaluate p_i(x) point-wise at log_n different x values.
	let mut v_mat = MatrixMN::ones(n as usize, log_n as usize);
	for i in 0..(n as usize) {
		for k in 0..(log_n as usize) {
			for j in 0..(log_n as usize) {
				let i_j = (i >> j) & 1;
				let l_j = ((idx as usize) >> j) & 1;
				let delta = 1 ^ i_j ^ l_j;
				v_mat[(i, k)] *= f[delta][i_j][(k, j)];
			}
		}
	}

	// Subtract away the only degree log_n monomial, ensuring all polynomials are degree <log_n.
	for k in 0..(log_n as usize) {
		v_mat[(idx as usize, k)] -= x_log_n_powers[k];
	}

	let x_powers_inv = x_powers_mat.clone().inverse()
		.expect("vandermonde matrix with distinct, non-zero points must be invertible");
	&v_mat * &(x_powers_inv.transpose().into())
}

fn inner_product<'a, IA, IB>(a: IA, b: IB) -> Scalar
	where
		IA: Iterator,
		IA::Item: Borrow<Scalar>,
		IB: Iterator,
		IB::Item: Borrow<Scalar>,
{
	a.zip(b).fold(Scalar::zero(), |prod, (a_i, b_i)| prod + a_i.borrow() * b_i.borrow())
}

fn challenge_scalar(transcript: &mut Transcript, label: &'static [u8]) -> Scalar {
	let mut bytes = [0u8; 64];
	transcript.challenge_bytes(label, &mut bytes);
	Scalar::from_bytes_mod_order_wide(&bytes)
}

#[cfg(test)]
mod tests {
	use super::*;

	use rand::{Rng, SeedableRng, rngs::StdRng};

	#[test]
	fn prove_and_verify() {
		let mut rng = StdRng::seed_from_u64(0);
		let params = PublicParams {
			label: b"TEST PROOF",
			g: RistrettoPoint::random(&mut rng),
			h: RistrettoPoint::random(&mut rng),
		};

		let keys = (0..25)
			.map(|_| Scalar::random(&mut rng))
			.collect::<Vec<_>>();
		let pubkeys = keys.iter()
			.map(|x| x * params.g)
			.collect::<Vec<_>>();

		let idx = rng.gen_range(0, keys.len());

		let proof = prove(&params, &mut rng, &pubkeys, idx as u32, keys[idx]).unwrap();
		assert!(verify(&params, &mut rng, &pubkeys, &proof).unwrap());
	}
}
