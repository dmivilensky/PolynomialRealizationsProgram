import krylov.Methods.ProjectedSearch
import krylov.LinearAlgebra.SpectralConditioning

/-!
Article: main_krylov, lem:projected-residual, projection onto the next recorded window.
Use: prove that the actual combined line/correction step has bounded normalized
coordinates in the augmented window, uniformly in its physical length.
Source: the genuine normalized Gram lower bound and finite Euclidean Cauchy--Schwarz.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- Pairing an actual synthesized correction is the Euclidean pairing of its coefficients with the projected gradient.
Use: control the new recorded unit-step coordinate by the augmented residual.
Article: main_krylov, lem:projected-residual.
Proof: expand the physical finite sum and the genuine Euclidean coefficient inner product. -/
theorem combine_inner_coordinates (s : Fin p → E) (c : Fin p → ℝ) (g : E) :
    inner ℝ (combine s c) g=inner ℝ (WithLp.toLp 2 c) (projectedResidual s g) := by
  simp only [combine, sum_inner, real_inner_smul_left, projectedResidual,
    EuclideanSpace.inner_toLp_toLp, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The true normalized Gram lower endpoint bounds physical synthesis coefficients.
Use: no raw-step inverse enters the next recorded-unit-step estimate.
Article: main_krylov, lem:projected-residual, bounded new coordinates in T.
Proof: the genuine lower spectral form equals the actual synthesis energy;
take nonnegative square roots and divide by the positive square root of a. -/
theorem combine_coefficients_bound (s : Fin p → E) (c : Fin p → ℝ) {a : ℝ} (ha : 0<a)
    (hgram : ∀ i, a≤(crossGram_isHermitian s).eigenvalues i) :
    ‖WithLp.toLp 2 c‖≤(Real.sqrt a)⁻¹*‖combine s c‖ := by
  -- The lower form is tested on the real coefficient vector used to synthesize the correction.
  have he := spectral_lower_form (crossGram s s) (crossGram_isHermitian s) hgram (WithLp.toLp 2 c)
  rw [← combine_norm_sq] at he
  have hp : 0<Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [← div_eq_inv_mul, le_div_iff₀ hp]
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hp.le) (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt ha.le, mul_comm]
  exact he

/-- Dropping the first coordinate decreases the actual Euclidean residual norm.
Use: old retained columns are unchanged after recording the combined RFC step.
Article: main_krylov, lem:projected-residual.
Proof: its omitted real squared coordinate is nonnegative. -/
theorem coordinate_tail_norm_le (v : Fin (p+1) → ℝ) :
    ‖WithLp.toLp 2 (fun i : Fin p => v i.succ)‖≤‖WithLp.toLp 2 v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- An actual Euclidean residual is bounded by its first absolute coordinate plus its old-coordinate norm.
Use: combine the new recorded-step coordinate estimate with the unchanged old window.
Article: main_krylov, lem:projected-residual.
Proof: split its finite energy sum and compare nonnegative squared norms. -/
theorem coordinate_norm_le_head_tail (v : Fin (p+1) → ℝ) :
    ‖WithLp.toLp 2 v‖≤|v 0|+‖WithLp.toLp 2 (fun i : Fin p => v i.succ)‖ := by
  -- The triangle-type bound follows directly from the genuine Euclidean energy decomposition.
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (abs_nonneg _) (norm_nonneg _))).mp
  have he : ‖WithLp.toLp 2 v‖^2=(v 0)^2+
      ‖WithLp.toLp 2 (fun i : Fin p => v i.succ)‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  nlinarith [sq_abs (v 0), mul_nonneg (abs_nonneg (v 0))
    (norm_nonneg (WithLp.toLp 2 (fun i : Fin p => v i.succ)))]

/-- The actual recorded unit step and retained old unit columns have a uniformly bounded residual transfer.
Use: converts the augmented normalized correction residual into the source's R₊.
Article: main_krylov, lem:projected-residual, the final recorded-window estimate.
Proof: the new step is the actual line plus the synthesized correction;
the relative-correction bound controls their coefficients, and Cauchy--Schwarz
then bounds its new unit pairing beside the unchanged old coordinates. -/
theorem recorded_residual_bound (s : Fin (p+1) → E) (c : Fin (p+1) → ℝ)
    (g : E) (l : ℝ) {K L : ℝ} (hL : 0≤L) (hs : ‖s 0‖=1)
    (hc : ‖WithLp.toLp 2 c‖≤L*‖combine s c‖)
    (hv : l • s 0+combine s c≠0)
    (hχ : ‖combine s c‖≤K*‖l • s 0+combine s c‖) :
    ‖projectedResidual (Fin.cons
      (‖l • s 0+combine s c‖⁻¹ • (l • s 0+combine s c)) (fun i : Fin p => s i.succ)) g‖≤
      (2+K+L*K)*‖projectedResidual s g‖ := by
  -- The coefficient bound is relative to the actual recorded movement, not to the possibly tiny line.
  let v := l • s 0+combine s c
  have hp : 0<‖v‖ := norm_pos_iff.mpr hv
  have hl : |l|≤‖v‖+‖combine s c‖ := by
    have ht := norm_sub_le v (combine s c)
    rw [show v-combine s c=l • s 0 by dsimp only [v]; abel, norm_smul,
      Real.norm_eq_abs, hs, mul_one] at ht
    exact ht
  have hcoef : |l|+‖WithLp.toLp 2 c‖≤(1+K+L*K)*‖v‖ := by
    have hc' := hc.trans (mul_le_mul_of_nonneg_left hχ hL)
    dsimp only [v] at hl ⊢
    nlinarith
  have hhead : |inner ℝ (‖v‖⁻¹ • v) g|≤(1+K+L*K)*‖projectedResidual s g‖ := by
    have ho : |inner ℝ (s 0) g|≤‖projectedResidual s g‖ := by
      simpa only [projectedResidual, coordinates, Real.norm_eq_abs] using
        PiLp.norm_apply_le (projectedResidual s g) 0
    have hi := norm_inner_le_norm (𝕜 := ℝ) (WithLp.toLp 2 c) (projectedResidual s g)
    rw [Real.norm_eq_abs, ← combine_inner_coordinates] at hi
    have ht : |inner ℝ v g|≤((1+K+L*K)*‖v‖)*‖projectedResidual s g‖ := by
      change |inner ℝ (l • s 0+combine s c) g|≤_
      rw [inner_add_left, real_inner_smul_left]
      calc
        _ ≤ |l| * |inner ℝ (s 0) g|+|inner ℝ (combine s c) g| := by
          simpa only [abs_mul] using abs_add_le (l*inner ℝ (s 0) g) (inner ℝ (combine s c) g)
        _ ≤ |l| * ‖projectedResidual s g‖+‖WithLp.toLp 2 c‖*‖projectedResidual s g‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ho (abs_nonneg _)) hi
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoef (norm_nonneg (projectedResidual s g))]
    rw [real_inner_smul_left, abs_mul, abs_of_nonneg (inv_nonneg.mpr hp.le)]
    exact (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hp.le)).trans_eq
      (by rw [← mul_assoc, mul_left_comm ‖v‖⁻¹, inv_mul_cancel₀ hp.ne', mul_one])
  have ht := coordinate_norm_le_head_tail (coordinates (Fin.cons (‖v‖⁻¹ • v)
    (fun i : Fin p => s i.succ)) g)
  have hold := coordinate_tail_norm_le (coordinates s g)
  change ‖projectedResidual _ g‖≤_ at ht
  simp only [coordinates, Fin.cons_zero, Fin.cons_succ] at ht
  exact (ht.trans (add_le_add hhead hold)).trans_eq (by change _+‖projectedResidual s g‖=_; ring)

end
end krylov.Methods
