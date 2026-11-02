import krylov.XR.LocalRawWindow
import krylov.XR.AlgorithmModel

/-!
Article: main_krylov, proof of thm:XR and apG:local.
Use: bound the genuine observed generalized Ritz values from unit-step
independence and actual relative secant errors. These are estimates for
the real latest-information matrix, not an assumed spectral enclosure.
Source: the proved p-epsilon matrix error, Cauchy--Schwarz and the physical
Rayleigh quotient of the true limiting Hessian.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Secant krylov.Convergence
open krylov.Methods hiding unitWindow unitWindow_norm unitWindow_diagonal_unit
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Actual generalized Rayleigh values before packaging them as a list. -/
def windowRayleighValues (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) : Set ℝ :=
  {r | ∃ c : Fin p → ℝ, c ≠ 0 ∧ r = (c ⬝ᵥ (T *ᵥ c)) / ‖combine s c‖ ^ 2}

/-- Every actual normalized Rayleigh quotient differs from the true
physical Hessian quotient by at most p epsilon / sigma². -/
theorem unitWindow_rayleigh_error (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (sigma epsilon : ℝ) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hgain : ∀ c : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 c‖ ^ 2 ≤ ‖combine s c‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon) (c : Fin p → ℝ) (hc : c ≠ 0) :
    |(c ⬝ᵥ (latest (crossGram s y) *ᵥ c)) / ‖combine s c‖ ^ 2 -
      inner ℝ (H (combine s c)) (combine s c) / ‖combine s c‖ ^ 2| ≤
        (p : ℝ) * epsilon / sigma ^ 2 := by
  have hnorm : 0 < ‖WithLp.toLp 2 c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
    (fun hz => hc (WithLp.toLp_injective 2 hz)))
  have hcomb : 0 < ‖combine s c‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos hsigma) hnorm) (hgain c)
  have hm := coefficient_quadratic_norm_bound
    (latest (crossGram s y) - localReferenceGram H s) c
  have herr := local_latest_error_norm H hH s y hs he hy
  have heq : c ⬝ᵥ ((latest (crossGram s y) - localReferenceGram H s) *ᵥ c) =
      c ⬝ᵥ (latest (crossGram s y) *ᵥ c) - inner ℝ (H (combine s c)) (combine s c) := by
    rw [sub_mulVec, dotProduct_sub, localReferenceGram, operatorGram_form]
  rw [heq] at hm
  have hb : |c ⬝ᵥ (latest (crossGram s y) *ᵥ c) -
      inner ℝ (H (combine s c)) (combine s c)| ≤
      ((p : ℝ) * epsilon / sigma ^ 2) * ‖combine s c‖ ^ 2 := by
    calc
      _ ≤ ((p : ℝ) * epsilon) * ‖WithLp.toLp 2 c‖ ^ 2 :=
        hm.trans (mul_le_mul_of_nonneg_right herr (sq_nonneg _))
      _ = ((p : ℝ) * epsilon / sigma ^ 2) *
          (sigma ^ 2 * ‖WithLp.toLp 2 c‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgain c) (by positivity)
  rw [← sub_div, abs_div, abs_of_pos hcomb]
  exact (div_le_iff₀ hcomb).mpr hb

/-- Primitive physical Hessian and secant bounds enclose every genuine
observed unit-step generalized Ritz value. -/
theorem unitWindow_rayleigh_mem_Icc (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu upper sigma epsilon : ℝ) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hnorm : ‖H‖ ≤ upper)
    (hgain : ∀ c : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 c‖ ^ 2 ≤ ‖combine s c‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    {r : ℝ} (hr : r ∈ windowRayleighValues s (latest (crossGram s y))) :
    r ∈ Icc (mu - (p : ℝ) * epsilon / sigma ^ 2)
      (upper + (p : ℝ) * epsilon / sigma ^ 2) := by
  obtain ⟨c, hc, rfl⟩ := hr
  have herr := unitWindow_rayleigh_error H hH s y hs sigma epsilon hsigma he hgain hy c hc
  have hcn : 0 < ‖WithLp.toLp 2 c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
    (fun hz => hc (WithLp.toLp_injective 2 hz)))
  have hd : 0 < ‖combine s c‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos hsigma) hcn) (hgain c)
  have hl : mu ≤ inner ℝ (H (combine s c)) (combine s c) / ‖combine s c‖ ^ 2 :=
    (le_div_iff₀ hd).mpr (by simpa only [real_inner_comm] using hpositive (combine s c))
  have hu : inner ℝ (H (combine s c)) (combine s c) / ‖combine s c‖ ^ 2 ≤ upper := by
    apply (div_le_iff₀ hd).mpr
    calc
      _ ≤ ‖H (combine s c)‖ * ‖combine s c‖ := real_inner_le_norm _ _
      _ ≤ (‖H‖ * ‖combine s c‖) * ‖combine s c‖ :=
        mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
      _ ≤ upper * ‖combine s c‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖combine s c‖)]
  exact ⟨by linarith [(abs_le.mp herr).1], by linarith [(abs_le.mp herr).2]⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem rescaleModel_quadratic (T : Matrix (Fin p) (Fin p) ℝ)
    (d c : Fin p → ℝ) :
    c ⬝ᵥ (rescaleModel T d *ᵥ c) =
      (diagonal d *ᵥ c) ⬝ᵥ (T *ᵥ (diagonal d *ᵥ c)) := by
  rw [rescaleModel, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  congr 1
  ext i
  simp only [vecMul_diagonal, mulVec_diagonal]
  ring

/-- The actual unnormalized window has the same generalized Ritz
enclosure; genuine nonzero step normalization is discharged explicitly. -/
theorem rawWindow_rayleigh_mem_Icc (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, s i ≠ 0)
    (mu upper sigma epsilon : ℝ) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hnorm : ‖H‖ ≤ upper)
    (hgain : ∀ c : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 c‖ ^ 2 ≤ ‖combine (unitWindow s) c‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon * ‖s i‖)
    {r : ℝ} (hr : r ∈ windowRayleighValues s (latest (crossGram s y))) :
    r ∈ Icc (mu - (p : ℝ) * epsilon / sigma ^ 2)
      (upper + (p : ℝ) * epsilon / sigma ^ 2) := by
  obtain ⟨c, hc, rfl⟩ := hr
  let z : Fin p → ℝ := fun i => ‖s i‖ * c i
  have hz : diagonal (fun i => ‖s i‖⁻¹) *ᵥ z = c := by
    ext i
    simp only [mulVec_diagonal, z]
    field_simp [norm_ne_zero_iff.mpr (hs i)]
  have hz₀ : z ≠ 0 := by
    intro hzero
    rw [hzero, mulVec_zero] at hz
    exact hc hz.symm
  have hcomb : combine (unitWindow s) z = combine s c := by
    rw [unitWindow, combine_rescale, hz]
  have hquad : z ⬝ᵥ (latest (crossGram (unitWindow s) (unitWindowImages s y)) *ᵥ z) =
      c ⬝ᵥ (latest (crossGram s y) *ᵥ c) := by
    change z ⬝ᵥ (ss1Model (rescaleWindow s (fun i => ‖s i‖⁻¹))
      (rescaleWindow y (fun i => ‖s i‖⁻¹)) *ᵥ z) = _
    rw [ss1Model_rescale, rescaleModel_quadratic, hz]
    rfl
  apply unitWindow_rayleigh_mem_Icc H hH (unitWindow s) (unitWindowImages s y)
    (unitWindow_norm s hs) mu upper sigma epsilon hsigma he hpositive hnorm hgain
    (unitWindow_reference_error H s y hs epsilon hy)
  exact ⟨z, hz₀, by rw [hcomb, hquad]⟩

/-- The concrete observed Ritz set is nonempty whenever a real pair is
present. This also discharges the domain of its real extrema. -/
theorem observedRayleighValues_nonempty (W : List (PairObservation E)) (hW : 0 < W.length) :
    (observedRayleighValues W).Nonempty := by
  let i : Fin W.length := ⟨0, hW⟩
  let c : Fin W.length → ℝ := Pi.single i 1
  have hc : c ≠ 0 := by
    intro hzero
    have hi := congrFun hzero i
    simp only [c, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hi
  exact ⟨_, c, hc, rfl⟩

/-- True relative secant errors and physical G2 bound the literal
observed Ritz maximum used in the running upper-bound update. -/
theorem observedRitz_sup_le (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (W : List (PairObservation E)) (hW : 0 < W.length)
    (hs : ∀ i, storedSteps W i ≠ 0)
    (mu upper sigma epsilon : ℝ) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hnorm : ‖H‖ ≤ upper)
    (hgain : ∀ c : Fin W.length → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 c‖ ^ 2 ≤ ‖combine (unitWindow (storedSteps W)) c‖ ^ 2)
    (hy : ∀ i, ‖storedImages W i - H (storedSteps W i)‖ ≤ epsilon * ‖storedSteps W i‖) :
    sSup (observedRayleighValues W) ≤ upper + (W.length : ℝ) * epsilon / sigma ^ 2 := by
  apply csSup_le (observedRayleighValues_nonempty W hW)
  intro r hr
  exact (rawWindow_rayleigh_mem_Icc H hH (storedSteps W) (storedImages W) hs
    mu upper sigma epsilon hsigma he hpositive hnorm hgain hy hr).2

end
end krylov.XR
