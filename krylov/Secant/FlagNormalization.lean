import krylov.Secant.Metric
import krylov.LinearAlgebra.MatrixAsymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: Lemma A.3 [apA:lem:flagcd] of krylov.tex.
Use: replacing the observed diagonal by the positive reference energies costs
quadratic order for a first-order observed defect.
Source: differentiability of the real inverse square root away from zero,
mathlib's differentiable-function big-O estimate, and the actual matrix coordinate equivalence.
-/

namespace krylov.Secant
noncomputable section
open Matrix Filter Asymptotics Topology krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator
variable {α : Type*} {p : ℕ} {f : Filter α}

/-- Fixed positive energy normalization of an actual window form.
Use: C^(−1/2) Z C^(−1/2) and the reference normalization of the observed defect.
Article: main_krylov, apA:lem:flagcd(d), fixed reference C. -/
def fixedNormalize (c : Fin p → ℝ) (Z : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j => Z i j / (Real.sqrt (c i)*Real.sqrt (c j))

/-- The fixed entry normalization is the actual reference diagonal congruence.
Use: its matrix interpretation is the printed C^(−1/2) Z C^(−1/2).
Article: main_krylov, apA:lem:flagcd(d).
Proof: evaluate the two actual diagonal products and combine the scalar inverses. -/
theorem fixedNormalize_eq (c : Fin p → ℝ) (Z : Matrix (Fin p) (Fin p) ℝ) :
    fixedNormalize c Z = diagonal (fun i => (Real.sqrt (c i))⁻¹)*Z*
      diagonal (fun i => (Real.sqrt (c i))⁻¹) := by
  ext i j
  simp only [fixedNormalize, diagonal_mul, mul_diagonal, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

/-- A first-order scalar perturbation of a positive number has a first-order inverse-square-root change.
Use: the observed diagonal normalizer is a genuine smooth function of the actual data.
Article: main_krylov, apA:lem:flagcd(d), changing observed diagonal energies.
Proof: compose the differentiable inverse-square-root local estimate with the
actual scalar perturbation and its convergence to the positive reference. -/
theorem inverse_sqrt_first_order (a s : α → ℝ) {c : ℝ} (hc : 0<c)
    (hs : Tendsto s f (𝓝 0)) (ha : (fun x => a x-c) =O[f] s) :
    (fun x => (Real.sqrt (a x))⁻¹-(Real.sqrt c)⁻¹) =O[f] s := by
  have ht : Tendsto a f (𝓝 c) := by
    simpa only [sub_add_cancel, zero_add] using (ha.trans_tendsto hs).add_const c
  have hd : DifferentiableAt ℝ (fun y : ℝ => (Real.sqrt y)⁻¹) c :=
    ((differentiableAt_id.sqrt hc.ne').inv (Real.sqrt_pos.mpr hc).ne')
  exact (hd.isBigO_sub.comp_tendsto ht).trans ha

/-- Actual observed diagonal normalization changes a first-order defect only at quadratic order.
Use: the article's data-only δ and its fixed-energy first-order expansion agree to O(s²).
Article: main_krylov, apA:lem:flagcd(d), normalized defect remainder.
Proof: form the actual diagonal product, apply the proved smooth inverse-square-root
estimate, and multiply its first-order change by the actual first-order defect entry. -/
theorem canonicalDefect_normalization_order
    (M : α → Matrix (Fin p) (Fin p) ℝ) (c : Fin p → ℝ) (hc : ∀ i, 0<c i)
    (s : α → ℝ) (hs : Tendsto s f (𝓝 0))
    (hM : ∀ i, (fun x => M x i i-c i) =O[f] s)
    (hD : (fun x => defect (M x)) =O[f] s) :
    (fun x => canonicalDefect (M x)-fixedNormalize c (defect (M x))) =O[f]
      (fun x => s x^2) := by
  apply (matrix_bigO_iff_entry _ _).mpr
  intro i j
  have htj : Tendsto (fun x => M x j j) f (𝓝 (c j)) := by
    simpa only [sub_add_cancel, zero_add] using ((hM j).trans_tendsto hs).add_const (c j)
  have hj1 : (fun x => M x j j) =O[f] (fun _ => (1 : ℝ)) := htj.isBigO_one ℝ
  have hprod : (fun x => M x i i*M x j j-c i*c j) =O[f] s := by
    have h1 := (hM i).mul hj1
    have h2 := (hM j).const_mul_left (c i)
    have h1' : (fun x => (M x i i-c i)*M x j j) =O[f] s := by simpa only [mul_one] using h1
    exact (h1'.add h2).congr_left fun x => by ring
  have hn := inverse_sqrt_first_order (fun x => M x i i*M x j j) s (mul_pos (hc i) (hc j)) hs hprod
  have hd := (matrix_bigO_iff_entry _ _).mp hD i j
  have h := hd.mul hn
  simp only [← pow_two] at h
  -- Only the reference product is split; the perturbed product is kept as the true observed denominator.
  apply h.congr_left
  intro x
  simp only [Matrix.sub_apply, canonicalDefect, fixedNormalize,
    Real.sqrt_mul (le_of_lt (hc i)), div_eq_mul_inv]
  ring

end
end krylov.Secant
