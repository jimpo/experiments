use criterion::{Criterion, criterion_group, criterion_main};
use curve25519_dalek::{
	ristretto::RistrettoPoint,
	scalar::Scalar,
};
use merlin::Transcript;
use rand::{Rng, thread_rng};
use ring_signatures::{
	PublicParams, VerifyCondition,
	compute_p_coefficients, prove, verify, precompute_verifier_static_points, serialize_points,
};

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

fn bench_verify_one(c: &mut Criterion) {
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
	let proof = prove(&params, &mut rng, &pubkeys, idx as u32, keys[idx]).unwrap();

	let mut partial_transcript = Transcript::new(params.label);
	partial_transcript.append_message(b"RING", &serialize_points(&pubkeys));

	let static_points = precompute_verifier_static_points(&params, &pubkeys);

	c.bench_function("verify without conditions check", |b| {
		b.iter(|| {
			verify(partial_transcript.clone(), pubkeys.len(), &proof).unwrap();
		})
	});

	c.bench_function("verify one", |b| {
		b.iter(|| {
			let conditions = verify(partial_transcript.clone(), pubkeys.len(), &proof).unwrap();
			assert!(VerifyCondition::verify_many(&mut rng, &static_points, conditions));
		})
	});
}

fn bench_verify_many(c: &mut Criterion) {
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

	let proofs = (0..RING_SIZE)
		.map(|idx| {
			prove(&params, &mut rng, &pubkeys, idx as u32, keys[idx])
				.unwrap()
		})
		.collect::<Vec<_>>();

	let mut partial_transcript = Transcript::new(params.label);
	partial_transcript.append_message(b"RING", &serialize_points(&pubkeys));

	let static_points = precompute_verifier_static_points(&params, &pubkeys);

	c.bench_function("verify many", |b| {
		b.iter(|| {
			let conditions = proofs.iter()
				.flat_map(|proof| {
					verify(partial_transcript.clone(), pubkeys.len(), proof)
						.unwrap()
						.into_iter()
				})
				.collect::<Vec<_>>();
			assert!(VerifyCondition::verify_many(&mut rng, &static_points, conditions));
		})
	});
}

criterion_group! {
	name = fast;
	config = Criterion::default();
	targets = bench_verify_one,
}
criterion_group! {
	name = slow;
	config = Criterion::default()
		.sample_size(10);
	targets = bench_verify_one,
}
criterion_main!(fast, slow);