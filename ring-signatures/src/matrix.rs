use curve25519_dalek::scalar::Scalar;
use std::convert::{TryInto, TryFrom};
use std::ops::{Add, Index, IndexMut, Mul, Neg, Sub};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatrixMN {
	m: usize,
	n: usize,
	inner: Vec<Scalar>,
}

impl MatrixMN {
	pub fn zeros(m: usize, n: usize) -> MatrixMN {
		MatrixMN {
			m,
			n,
			inner: vec![Scalar::zero(); m * n],
		}
	}

	pub fn ones(m: usize, n: usize) -> MatrixMN {
		MatrixMN {
			m,
			n,
			inner: vec![Scalar::one(); m * n],
		}
	}

	pub fn m(&self) -> usize {
		self.m
	}

	pub fn n(&self) -> usize {
		self.n
	}

	pub fn get(&self, i: usize, j: usize) -> Option<&Scalar> {
		if i < self.m && j < self.n {
			Some(&self[(i, j)])
		} else {
			None
		}
	}

	pub fn get_mut(&mut self, i: usize, j: usize) -> Option<&mut Scalar> {
		if i < self.m && j < self.n {
			Some(&mut self[(i, j)])
		} else {
			None
		}
	}

	// This consumes self as it is possible to implement in-place even though the current.
	pub fn transpose(mut self) -> Self {
		let mut output = MatrixMN::zeros(self.n, self.m);
		for i in 0..self.m {
			for j in 0..self.n {
				output[(j, i)] = self[(i, j)];
			}
		}
		output
	}
}

impl Index<(usize, usize)> for MatrixMN {
	type Output = Scalar;

	fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
		&self.inner[i * self.n + j]
	}
}

impl IndexMut<(usize, usize)> for MatrixMN {
	fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
		&mut self.inner[i * self.n + j]
	}
}

impl From<MatrixNN> for MatrixMN {
	fn from(mat: MatrixNN) -> Self {
		mat.inner
	}
}

impl Add for &MatrixMN {
	type Output = MatrixMN;

	fn add(self, rhs: Self) -> Self::Output {
		if self.n != rhs.n || self.m != rhs.m {
			panic!("in matrix addition, addends must have same dimensions");
		}

		let mut out = MatrixMN::zeros(self.m, self.n);
		for i in 0..out.m {
			for j in 0..out.n {
				out[(i, j)] = self[(i, j)] + rhs[(i, j)];
			}
		}
		out
	}
}

impl Sub for &MatrixMN {
	type Output = MatrixMN;

	fn sub(self, rhs: Self) -> Self::Output {
		if self.n != rhs.n || self.m != rhs.m {
			panic!("in matrix subtraction, inputs must have same dimensions");
		}

		let mut out = MatrixMN::zeros(self.m, self.n);
		for i in 0..out.m {
			for j in 0..out.n {
				out[(i, j)] = self[(i, j)] - rhs[(i, j)];
			}
		}
		out
	}
}

impl Mul for &MatrixMN {
	type Output = MatrixMN;

	fn mul(self, rhs: Self) -> Self::Output {
		if self.n != rhs.m {
			panic!("in matrix multiplication, n of left-hand side must equal m of right-hand side");
		}

		let mut out = MatrixMN::zeros(self.m, rhs.n);
		for i in 0..out.m {
			for j in 0..out.n {
				for k in 0..self.n {
					out[(i, j)] += self[(i, k)] * rhs[(k, j)];
				}
			}
		}
		out
	}
}

impl Neg for &MatrixMN {
	type Output = MatrixMN;

	fn neg(self) -> Self::Output {
		let mut out = MatrixMN::zeros(self.m, self.n);
		for i in 0..out.m {
			for j in 0..out.n {
				out[(i, j)] = -self[(i, j)];
			}
		}
		out
	}
}

impl Add for MatrixMN {
	type Output = MatrixMN;

	fn add(self, rhs: Self) -> Self::Output {
		Add::add(&self, &rhs)
	}
}

impl Sub for MatrixMN {
	type Output = MatrixMN;

	fn sub(self, rhs: Self) -> Self::Output {
		Sub::sub(&self, &rhs)
	}
}

impl Mul for MatrixMN {
	type Output = MatrixMN;

	fn mul(self, rhs: Self) -> Self::Output {
		Mul::mul(&self, &rhs)
	}
}

impl Neg for MatrixMN {
	type Output = MatrixMN;

	fn neg(self) -> Self::Output {
		Neg::neg(&self)
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatrixNN {
	inner: MatrixMN,
}

impl MatrixNN {
	pub fn zeros(n: usize) -> MatrixNN {
		MatrixNN {
			inner: MatrixMN::zeros(n, n),
		}
	}

	pub fn ones(n: usize) -> MatrixNN {
		MatrixNN {
			inner: MatrixMN::ones(n, n),
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

	pub fn n(&self) -> usize {
		self.inner.n()
	}

	pub fn get(&self, i: usize, j: usize) -> Option<&Scalar> {
		self.inner.get(i, j)
	}

	pub fn get_mut(&mut self, i: usize, j: usize) -> Option<&mut Scalar> {
		self.inner.get_mut(i, j)
	}

	pub fn inverse(mut self) -> Option<MatrixNN> {
		let n = self.n();
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
		for j in 0..self.n() {
			self[(i, j)] *= x;
		}
	}

	fn add_rows(&mut self, i1: usize, i2: usize, x: &Scalar, start_col: usize) {
		for j in start_col..self.n() {
			let y = self[(i2, j)] * x;
			self[(i1, j)] += y;
		}
	}

	pub fn transpose(mut self) -> Self {
		for i in 0..self.n() {
			for j in (i + 1)..self.n() {
				let tmp = self[(i, j)];
				self[(i, j)] = self[(j, i)];
				self[(j, i)] = tmp;
			}
		}
		self
	}
}

impl Index<(usize, usize)> for MatrixNN {
	type Output = Scalar;

	fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
		Index::index(&self.inner, (i, j))
	}
}

impl IndexMut<(usize, usize)> for MatrixNN {
	fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
		IndexMut::index_mut(&mut self.inner, (i, j))
	}
}

impl TryFrom<MatrixMN> for MatrixNN {
	type Error = ();

	fn try_from(mat: MatrixMN) -> Result<Self, ()> {
		if mat.m == mat.n {
			Ok(MatrixNN { inner: mat })
		} else {
			Err(())
		}
	}
}

impl Add for &MatrixNN {
	type Output = MatrixNN;

	fn add(self, rhs: Self) -> Self::Output {
		Add::add(&self.inner, &rhs.inner)
			.try_into()
			.expect("dimensions of output are the same as input, which is n x n")
	}
}

impl Sub for &MatrixNN {
	type Output = MatrixNN;

	fn sub(self, rhs: Self) -> Self::Output {
		Sub::sub(&self.inner, &rhs.inner)
			.try_into()
			.expect("dimensions of output are the same as input, which is n x n")
	}
}

impl Mul for &MatrixNN {
	type Output = MatrixNN;

	fn mul(self, rhs: Self) -> Self::Output {
		Mul::mul(&self.inner, &rhs.inner)
			.try_into()
			.expect("dimensions of output are the same as input, which is n x n")
	}
}

impl Neg for &MatrixNN {
	type Output = MatrixNN;

	fn neg(self) -> Self::Output {
		Neg::neg(&self.inner)
			.try_into()
			.expect("dimensions of output are the same as input, which is n x n")
	}
}

impl Add for MatrixNN {
	type Output = MatrixNN;

	fn add(self, rhs: Self) -> Self::Output {
		Add::add(&self, &rhs)
	}
}

impl Sub for MatrixNN {
	type Output = MatrixNN;

	fn sub(self, rhs: Self) -> Self::Output {
		Sub::sub(&self, &rhs)
	}
}

impl Mul for MatrixNN {
	type Output = MatrixNN;

	fn mul(self, rhs: Self) -> Self::Output {
		Mul::mul(&self, &rhs)
	}
}

impl Neg for MatrixNN {
	type Output = MatrixNN;

	fn neg(self) -> Self::Output {
		Neg::neg(&self)
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
