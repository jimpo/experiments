use curve25519_dalek::scalar::Scalar;
use std::fmt;
use std::ops::{Index, IndexMut, Mul};

#[derive(Debug, Clone, PartialEq, Eq)]
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

	pub fn identity(n: usize) -> MatrixNN {
		let mut mat = Self::zeros(n);
		for i in 0..n {
			mat[(i, i)] = Scalar::one();
		}
		mat
	}

	pub fn vandermonde(elements: &[Scalar]) -> MatrixNN {
		let n = elements.len();
		let mut mat = Self::zeros(n);
		for i in 0..n {
			mat[(i, 0)] = Scalar::one();
			for j in 1..n {
				mat[(i, j)] = mat[(i, j - 1)] * elements[i];
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

	pub fn inverse(mut self) -> Option<MatrixNN> {
		let n = self.n;
		let mut inv = MatrixNN::identity(n);

		for i in 0..n {
			let x = self[(i, i)];
			if x == Scalar::zero() {
				return None
			}
			let x_inv = x.invert();
			self.scale_row(i, &x_inv);
			inv.scale_row(i, &x_inv);

			for ii in 0..n {
				if i != ii {
					let scalar = -self[(ii, i)];
					self.add_rows(ii, i, &scalar, i);
					inv.add_rows(ii, i, &scalar, 0);
				}
			}
		}

		assert_eq!(self, MatrixNN::identity(n));
		Some(inv)
	}

	fn scale_row(&mut self, i: usize, x: &Scalar) {
		for j in 0..self.n {
			self[(i, j)] *= x;
		}
	}

	fn add_rows(&mut self, i1: usize, i2: usize, x: &Scalar, start_col: usize) {
		for j in start_col..self.n {
			let y = self[(i2, j)] * x;
			self[(i1, j)] += y;
		}
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

impl Mul for MatrixNN {
	type Output = MatrixNN;

	fn mul(self, rhs: Self) -> Self::Output {
		Mul::mul(&self, &rhs)
	}
}

impl Mul for &MatrixNN {
	type Output = MatrixNN;

	fn mul(self, rhs: Self) -> Self::Output {
		let n = self.n;
		let mut out = MatrixNN::zeros(n);
		for i in 0..n {
			for j in 0..n {
				for k in 0..n {
					out[(i, j)] += self[(i, k)] * rhs[(k, j)];
				}
			}
		}
		out
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_vandermonde_inverse() {
		let elements = (1u32..=25u32)
			.map(Scalar::from)
			.collect::<Vec<_>>();
		let mat = MatrixNN::vandermonde(&elements);
		let mat_inv = mat.clone().inverse().unwrap();
		assert_eq!(mat * mat_inv, MatrixNN::identity(25));
	}
}
