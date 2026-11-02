import jacobi.Finite.Basic
import chebyshev2.Green.Contractivity

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Arbitrary monic terminal polynomials share the existing Jacobi matrix and energy.
The Chebyshev Terminal predicate is deliberately absent from every theorem here.
The trace and Cauchy--Schwarz estimates are the finite inputs to Section 6.
Use: the spectral weight chart and the persymmetric construction use this fibre.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Polynomial Matrix
open scoped BigOperators

/-- The monic fibre of an arbitrary terminal polynomial, with positive couplings.
Use: the spectral weight chart and the persymmetric construction use this fibre.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def InFiber {N : ℕ} (J : Jacobi N) (p : ℝ[X]) : Prop :=
  J.Irreducible ∧ J.matrix.charpoly = p

/-- Matrices in the monic fibre, retaining the canonical finite coefficient extension.
Use: packages the domain of the energy minimization and weight reconstruction.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
abbrev Fiber (N : ℕ) (p : ℝ[X]) := {J : Jacobi N // InFiber J p}

/-- Descending spectral nodes in the open interval of admissible terminal roots.
Use: specifies the polynomial and supplies contractivity to the packing theorem.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
structure Nodes (N : ℕ) where
  /-- The roots, indexed in the descending order used by the article. -/
  value : Fin N → ℝ
  /-- Distinct roots in descending order. -/
  strictAnti : StrictAnti value
  /-- Both affine pencils I ± J are positive on this spectrum. -/
  interval : ∀ i, value i ∈ Set.Ioo (-1) 1

namespace Nodes
variable {N : ℕ} (S : Nodes N)

/-- The monic polynomial with these ordered nodes.
Use: defines the arbitrary fibre without committing to a special polynomial family.
Article: jacobi, Proposition 2.2.
-/
def polynomial : ℝ[X] := ∏ i, (X - C (S.value i))

/-- Its value at the resolvent endpoint is strictly positive.
Use: justifies the logarithmic derivative and resolvent denominators.
Article: jacobi, Proposition 2.2.
Proof: every factor 1 − ζᵢ is positive. -/
theorem endpoint_pos : 0 < S.polynomial.eval 1 := by
  simp only [polynomial, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (S.interval i).2)

/-- A member of this fibre has exactly the prescribed spectrum.
Use: derives admissibility of the two affine pencils for all fibre matrices.
Article: jacobi, Lemma 1.3.
Proof: spectrum membership is a root of the characteristic polynomial. -/
theorem spectrum_eq {J : Jacobi N} (hJ : InFiber J S.polynomial) :
    spectrum ℝ J.matrix = Set.range S.value := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hJ.2]
  simp only [Polynomial.IsRoot, polynomial, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero, Set.mem_range]
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi.symm⟩

/-- Every matrix in the arbitrary fibre is strictly contractive.
Use: invokes the already proved geometric packing, including its block machinery.
Article: jacobi, Proposition 6.1.
Proof: the finite spectral theorem makes I ± J positive definite. -/
theorem contractive {J : Jacobi N} (hJ : InFiber J S.polynomial) : opNorm J.matrix < 1 := by
  -- The prescribed spectrum lies inside (-1,1), so both affine pencils are positive definite.
  have hi (x : ℝ) (hx : x ∈ spectrum ℝ J.matrix) : x ∈ Set.Ioo (-1) 1 := by
    rw [S.spectrum_eq hJ] at hx
    obtain ⟨i, rfl⟩ := hx
    exact S.interval i
  apply J.contractive_of_pencils
  · have h := J.affine_posDef 1 (-1) (fun x hx => by linarith [(hi x hx).2])
    simpa [Matrix.scalar, sub_eq_add_neg] using h
  · have h := J.affine_posDef 1 1 (fun x hx => by linarith [(hi x hx).1])
    simpa [Matrix.scalar] using h

end Nodes

/-- The resolvent trace is the logarithmic derivative of any characteristic polynomial.
Use: fixes the mass for a complete arbitrary-polynomial fibre.
Article: jacobi, Proposition 6.1.
Proof: diagonalize the matrix and use the library logarithmic derivative formula. -/
theorem green_trace {N : ℕ} (J : Jacobi N) (hp : J.matrix.charpoly.eval 1 ≠ 0) :
    Matrix.trace J.green =
      J.matrix.charpoly.derivative.eval 1 / J.matrix.charpoly.eval 1 := by
  -- Use the spectral theorem and the polynomial logarithmic derivative for the same characteristic roots.
  let hM := J.matrix_isHermitian
  have hlog := hM.splits_charpoly.eval_derivative_div_eval_of_ne_zero hp
  rw [hM.roots_charpoly_eq_eigenvalues] at hlog
  have heigs (i : Fin N) : 1 - hM.eigenvalues i ≠ 0 := by
    intro hz
    have he : hM.eigenvalues i = 1 := by linarith
    have hr := Matrix.mem_spectrum_iff_isRoot_charpoly.mp (hM.eigenvalues_mem_spectrum_real i)
    exact hp (by simpa [Polynomial.IsRoot, he] using hr)
  rw [Jacobi.green, SpectralCoordinates.trace_resolvent (SpectralBasis.ofHermitian _ hM) heigs]
  simpa [Multiset.map_map, Function.comp_def, Finset.sum, one_div, SpectralBasis.ofHermitian]
    using hlog.symm

/-- Cauchy--Schwarz bounds the resolvent energy by its fixed trace.
Use: gives the universal finite lower bound before spectral calibration.
Article: jacobi, Proposition 2.2.
Proof: apply finite Cauchy--Schwarz to the diagonal and the constant vector. -/
theorem trace_sq_le_energy {N : ℕ} (J : Jacobi N) :
    (Matrix.trace J.green)^2 ≤ (N : ℝ) * J.energy := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _i : Fin N => (1 : ℝ))
    (fun i => J.green i i)
  simpa [Matrix.trace, Jacobi.energy] using h

/-- The arbitrary-polynomial finite lower bound in its printed normalization.
Use: supplies the baseline n³ scaling in the introduction and Section 6.
Article: jacobi, Proposition 2.2.
Proof: substitute the logarithmic derivative into finite Cauchy--Schwarz. -/
theorem energy_lower {N : ℕ} (J : Jacobi N) (hN : 0 < N)
    (hp : J.matrix.charpoly.eval 1 ≠ 0) :
    (J.matrix.charpoly.derivative.eval 1 / J.matrix.charpoly.eval 1)^2 / (N : ℝ) ≤
      J.energy := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr hN), ← green_trace J hp]
  simpa only [mul_comm] using trace_sq_le_energy J

end
end jacobi.Finite
