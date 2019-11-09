use curve25519_dalek::scalar::Scalar;
use std::ops::{Index, IndexMut};

pub struct MatrixNN {
	n: usize,
	inner: Vec<Scalar>,
}

impl MatrixNN {
	pub fn zeros(n: usize) -> MatrixNN {
		MatrixNN {
			n,
			inner: vec![Scalar::zero(); n * n],
		}
	}

	pub fn ones(n: usize) -> MatrixNN {
		MatrixNN {
			n,
			inner: vec![Scalar::one(); n * n],
		}
	}

	pub fn vandermonde(elements: &[Scalar]) -> MatrixNN {
		let n = elements.len();
		let mut mat = Self::zeros(n);
		for i in 0..n {
			mat[(i, 0)] = Scalar::one();
			for j in 1..n {
				mat[(i, j)] = mat[(i, j)] * elements[i];
			}
		}
		mat
	}

	pub fn get(&self, i: usize, j: usize) -> Option<&Scalar> {
		self.inner.get(i * self.n + j)
	}

	pub fn get_mut(&mut self, i: usize, j: usize) -> Option<&mut Scalar> {
		self.inner.get_mut(i * self.n + j)
	}
}

impl Index<(usize, usize)> for MatrixNN {
	type Output = Scalar;

	fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
		&self.inner[i * self.n + j]
	}
}

impl IndexMut<(usize, usize)> for MatrixNN {
	fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
		&mut self.inner[i * self.n + j]
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_vandermonde() {
		let elements = (0u32..20u32)
			.map(Scalar::from)
			.collect::<Vec<_>>();
		MatrixNN::vandermonde(&elements);
	}
}
