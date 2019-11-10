use curve25519_dalek::scalar::Scalar;

pub struct ScalarPowersIterator {
	x: Scalar,
	next: Scalar,
}

impl ScalarPowersIterator {
	pub fn new(x: Scalar) -> Self {
		ScalarPowersIterator {
			x,
			next: Scalar::one(),
		}
	}
}

impl Iterator for ScalarPowersIterator {
	type Item = Scalar;

	fn next(&mut self) -> Option<Self::Item> {
		let output = self.next;
		self.next *= self.x;
		Some(output)
	}
}
