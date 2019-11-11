use criterion::{Criterion, criterion_group, criterion_main};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use rand::{Rng, thread_rng};
use ring_signatures::{PublicParams, compute_p_coefficients, prove, verify};

const RING_SIZE: usize = 1000;

fn bench_compute_p_coefficients(c: &mut Criterion) {
	let mut rng = thread_rng();

	let log_n = 32 - (RING_SIZE as u32 - 1).leading_zeros();
	let n = 1 << log_n;
	let a = (0..log_n)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();

	c.bench_function("compute p coefficients", |b| {
		b.iter(|| {
			let idx = rng.gen_range(0, RING_SIZE);
			compute_p_coefficients(n, log_n, idx as u32, &a);
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

	let keys = (0..RING_SIZE)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let pubkeys = keys.iter()
		.map(|x| x * params.g)
		.collect::<Vec<_>>();

	c.bench_function("prover", |b| {
		b.iter(|| {
			let idx = rng.gen_range(0, RING_SIZE);
			prove(&params, &mut rng, &pubkeys, idx as u32, keys[idx])
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

	let keys = (0..RING_SIZE)
		.map(|_| Scalar::random(&mut rng))
		.collect::<Vec<_>>();
	let pubkeys = keys.iter()
		.map(|x| x * params.g)
		.collect::<Vec<_>>();

	let idx = rng.gen_range(0, RING_SIZE);
	let proof = prove(&params, &mut rng, &pubkeys, idx as u32, keys[idx])
		.unwrap();

	c.bench_function("verifier", |b| {
		b.iter(|| {
			assert!(verify(&params, &mut rng, &pubkeys, &proof).unwrap());
		})
	});
}

criterion_group!(benches,
	bench_compute_p_coefficients,
	bench_prover,
	bench_verifier,
);
criterion_main!(benches);