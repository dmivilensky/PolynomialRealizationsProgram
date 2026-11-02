import krylov.Convergence.WindowNormalization
import krylov.Convergence.SlidingFCResidual
import krylov.XR.LocalCoercivity

/-!
Article: main_krylov, thm:Ip, automatic RFC probe-frame independence.
Use: augment an originally independent rectangular stored window by its
actual nearly orthogonal probe, and derive the full model inverse domain.
Source: the exact Gram block form and Cauchy--Schwarz. Independence of the
augmented frame is a conclusion, never an extra source assumption.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {p : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Chronological augmentation separates the genuine old coefficients and
the current probe coefficient exactly. -/
theorem combine_snoc_window (s : Fin p → E) (d : E) (c : Fin (p+1) → ℝ) :
    combine (Fin.snoc s d) c=combine s (fun i=>c i.castSucc)+c (Fin.last p) • d := by
  simp only [combine,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

/-- The coefficient Euclidean norm splits into old and current squares. -/
theorem coefficient_norm_snoc_sq (c : Fin (p+1) → ℝ) :
    ‖WithLp.toLp 2 c‖^2=‖WithLp.toLp 2 (fun i : Fin p=>c i.castSucc)‖^2+c (Fin.last p)^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc]

/-- The actual current unit direction's small pairings with the stored
unit steps give the precise rectangular square-root coefficient bound. -/
theorem combine_pairing_bound (s : Fin p → E) (d : E) {ε : ℝ} (hε : 0≤ε)
    (hs : ∀ i,|inner ℝ (s i) d|≤ε) (c : Fin p → ℝ) :
    |inner ℝ (combine s c) d|≤Real.sqrt p*ε*‖WithLp.toLp 2 c‖ := by
  let r := WithLp.toLp 2 (coordinates s d)
  have hr : ‖r‖≤Real.sqrt p*ε := coordinate_norm_le_sqrt_card _ hε hs
  have he : inner ℝ (combine s c) d=inner ℝ (WithLp.toLp 2 c) r := by
    simp only [combine,sum_inner,real_inner_smul_left,r,coordinates,PiLp.inner_apply,
      RCLike.inner_apply,conj_trivial]
    exact Finset.sum_congr rfl fun i _=>mul_comm _ _
  rw [he]
  exact ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans
    (mul_le_mul_of_nonneg_left hr (norm_nonneg _))).trans_eq (by rw [mul_comm])

/-- The source's exact augmented least-gain squared estimate. In the RFC
application, ε is the actual vanishing normalized secant error.
The old lower gain is capped at one only to allow all dimensions uniformly. -/
theorem augmented_window_gain_sq (s : Fin p → E) (d : E) {σ ε : ℝ}
    (hσ : 0≤σ) (hσ₁ : σ≤1) (hε : 0≤ε) (hd : ‖d‖=1)
    (hgain : ∀ c : Fin p → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (horth : ∀ i,|inner ℝ (s i) d|≤ε) (c : Fin (p+1) → ℝ) :
    (σ^2-Real.sqrt p*ε)*‖WithLp.toLp 2 c‖^2≤‖combine (Fin.snoc s d) c‖^2 := by
  let a := c (Fin.last p)
  let b := WithLp.toLp 2 (fun i : Fin p=>c i.castSucc)
  have hp := combine_pairing_bound s d hε horth (fun i=>c i.castSucc)
  have hg := hgain (fun i=>c i.castSucc)
  have hn := norm_add_sq_real (combine s (fun i=>c i.castSucc)) (a • d)
  rw [norm_smul,hd,mul_one,Real.norm_eq_abs,sq_abs,real_inner_smul_right] at hn
  have hcross : -(Real.sqrt p*ε)*(a^2+‖b‖^2)≤
      2*a*inner ℝ (combine s (fun i=>c i.castSucc)) d := by
    have ha : -|a| * |inner ℝ (combine s (fun i=>c i.castSucc)) d|≤
        a*inner ℝ (combine s (fun i=>c i.castSucc)) d := by
      rw [neg_mul,←abs_mul]
      exact neg_abs_le _
    have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg a)
    have hyoung : 2*|a| * ‖b‖≤a^2+‖b‖^2 := by nlinarith only [sq_nonneg (|a|-‖b‖),sq_abs a]
    have hscale := mul_le_mul_of_nonneg_left hyoung (by positivity : 0≤Real.sqrt p*ε)
    dsimp only [b] at hscale ⊢
    nlinarith only [ha,hh,hscale]
  rw [combine_snoc_window,coefficient_norm_snoc_sq]
  have hσsq : σ^2≤1 := by nlinarith only [hσ,hσ₁]
  have hlast := mul_le_mul_of_nonneg_right hσsq (sq_nonneg a)
  change (σ^2-Real.sqrt p*ε)*(‖b‖^2+a^2)≤_
  change ‖combine s (fun i=>c i.castSucc)+a • d‖^2=_ at hn
  nlinarith only [hn,hg,hcross,hlast]

/-- Actual observed conjugacy turns the genuine relative pair error into
the current direction's small normalized step pairings. -/
theorem observed_conjugacy_unit_pairing (s y d : E) (hs : s≠0) (hd : d≠0)
    {ε : ℝ} (hy : ‖y-s‖≤ε*‖s‖) (ho : inner ℝ y d=0) :
    |inner ℝ (‖s‖⁻¹ • s) (‖d‖⁻¹ • d)|≤ε := by
  have he : inner ℝ (‖s‖⁻¹ • s) (‖d‖⁻¹ • d)=
      inner ℝ (‖s‖⁻¹ • (s-y)) (‖d‖⁻¹ • d) := by
    simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,ho,sub_zero]
  rw [he]
  have hsn : 0<‖s‖ := norm_pos_iff.mpr hs
  have hdn : ‖‖d‖⁻¹ • d‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)]
  have herr : ‖‖s‖⁻¹ • (s-y)‖≤ε := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,norm_sub_rev]
    have hh := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hsn.le)
    rw [mul_left_comm,inv_mul_cancel₀ hsn.ne',mul_one] at hh
    exact hh
  simpa only [Real.norm_eq_abs,hdn,mul_one] using
    (norm_inner_le_norm (𝕜:=ℝ) (‖s‖⁻¹ • (s-y)) (‖d‖⁻¹ • d)).trans
      (mul_le_mul_of_nonneg_right herr (norm_nonneg _))

/-- A positive genuine synthesis gain proves the full ambient inverse
domain and a common quantitative inverse bound, without assuming rank. -/
theorem full_window_inverse_of_gain
    (s : Fin (p+1) → EuclideanSpace ℝ (Fin (p+1))) {c : ℝ} (hc : 0<c)
    (hgain : ∀ w : Fin (p+1) → ℝ,c*‖WithLp.toLp 2 w‖^2≤‖combine s w‖^2) :
    IsUnit (windowMatrix s).det ∧‖(windowMatrix s)⁻¹‖≤c⁻¹+1 := by
  let V := windowMatrix s
  have hg (w : Fin (p+1) → ℝ) : c*‖WithLp.toLp 2 w‖^2≤w ⬝ᵥ ((Vᵀ*V)*ᵥw) := by
    have he := operatorGram_form (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (p+1)))) s w
    simp only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] at he
    rw [←crossGram_windowMatrix]
    rw [he]
    exact hgain w
  have hh := krylov.XR.coefficient_inverse_of_coercivity (Vᵀ*V) c hc hg
  have hv : IsUnit V.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply isUnit_iff_ne_zero.mp hh.1
    rw [det_mul,det_transpose,hz,mul_zero]
  refine ⟨hv,?_⟩
  rw [inverse_gram_norm] at hh
  have hp : 0≤c⁻¹ := inv_nonneg.mpr hc.le
  nlinarith only [hh.2,norm_nonneg (V⁻¹),sq_nonneg (‖V⁻¹‖-1),hp]

end
end krylov.Convergence
