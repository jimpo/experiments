use criterion::{Criterion, criterion_group, criterion_main};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use rand::{Rng, thread_rng};
use ring_signatures::{PublicParams, PrecomputedProofParams, compute_p_coefficients, prove, verify};

const RING_SIZE: usize = 1000;

fn bench_precompute_proof_params(c: &mut Criterion) {
	c.bench_function("precompute proof params", |b| {
		b.iter(|| {
			PrecomputedProofParams::for_ring_len(RING_SIZE)
				.unwrap();
		})
	});
}

fn bench_compute_p_coefficients(c: &mut Criterion) {
	let mut rng = thread_rng();
	let params = PrecomputedProofParams::for_ring_len(RING_SIZE)
		.unwrap();

	let log_n = params.n();
	let n = 1 << log_n;

	let a = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();

	c.bench_function("compute p coefficients", |b| {
		b.iter(|| {
			let idx = rng.gen_range(0, RING_SIZE);
			compute_p_coefficients(&params, n, log_n, idx as u32, &a)
				.unwrap();
		})
	});
}

fn bench_prover(c: &mut Criterion) {
	let mut rng = thread_rng();
	let params = PublicParams {
		label: b"TEST PROOF",
		g: RistrettoPoint::random(&mut rng),
		h: RistrettoPoint::random(&mut rng),
	};
	let proof_params = PrecomputedProofParams::for_ring_len(RING_SIZE)
		.unwrap();

	let keys = (0..RING_SIZE)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let pubkeys = keys.iter()
		.map(|x| x * params.g)
		.collect::<Vec<_>>();

	c.bench_function("prover", |b| {
		b.iter(|| {
			let idx = rng.gen_range(0, RING_SIZE);
			prove(&params, &proof_params, &mut rng, &pubkeys, idx as u32, keys[idx])
				.unwrap();
		})
	});
}

fn bench_verifier(c: &mut Criterion) {
	let mut rng = thread_rng();
	let params = PublicParams {
		label: b"TEST PROOF",
		g: RistrettoPoint::random(&mut rng),
		h: RistrettoPoint::random(&mut rng),
	};
	let proof_params = PrecomputedProofParams::for_ring_len(RING_SIZE)
		.unwrap();

	let keys = (0..RING_SIZE)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let pubkeys = keys.iter()
		.map(|x| x * params.g)
		.collect::<Vec<_>>();

	let idx = rng.gen_range(0, RING_SIZE);
	let proof = prove(&params, &proof_params, &mut rng, &pubkeys, idx as u32, keys[idx])
		.unwrap();

	c.bench_function("verifier", |b| {
		b.iter(|| {
			assert!(verify(&params, &mut rng, &pubkeys, &proof).unwrap());
		})
	});
}

criterion_group!(benches,
	bench_precompute_proof_params,
	bench_compute_p_coefficients,
	bench_verifier,
);
criterion_main!(benches);