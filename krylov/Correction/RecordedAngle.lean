import krylov.Stability.WeightedNormalization
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, thm:UCq and thm:UCg, actual recorded/full-window estimates.
Use: Close genuine finite-cycle angle and terminal-gradient bounds without
replacing observed columns by hypothetical reference vectors.
Source: proved weighted normalization, actual model residual identities,
true spectral Gram conditioning and the original full Euclidean reconstruction.
-/

namespace krylov.Correction
noncomputable section
open krylov.Methods krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A true correction smaller than the actual line displacement cannot cancel the full recorded step.
Use: Complete the actual uniform gated-RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, real recorded and full-window bounds.
Proof: A zero total displacement would make the actual line and correction norms equal, contradicting the strict relative bound.
-/
theorem recorded_step_nonzero (line χ : E) {q : ℝ}
    (hline : 0<‖line‖) (hq : q<1) (hχ : ‖χ‖≤q*‖line‖) : line+χ≠0 := by
  intro hz
  have he : line= -χ := eq_neg_of_add_eq_zero_left hz
  rw [he,norm_neg] at hline hχ
  nlinarith

/-- The true recorded unit step differs from its actual line direction by at most twice the genuine relative correction size.
Use: Complete the actual uniform gated-RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, real recorded and full-window bounds.
Proof: Prove the actual total step nonzero first, then reuse the weighted normalization estimate with the true line norm and its exact unit direction.
-/
theorem recorded_step_normalized_change (line χ : E) {q : ℝ}
    (hline : 0<‖line‖) (hq : q<1) (hχ : ‖χ‖≤q*‖line‖) :
    ‖NormedSpace.normalize (line+χ)-NormedSpace.normalize line‖≤2*q := by
  have hv := recorded_step_nonzero line χ hline hq hχ
  have hl : line≠0 := norm_pos_iff.mp hline
  have hw := normalization_weighted (line+χ) (NormedSpace.normalize line) hv
    (NormedSpace.norm_normalize hl) ‖line‖ hline
  rw [NormedSpace.norm_smul_normalize,add_sub_cancel_left] at hw
  nlinarith

/-- The actual recorded step preserves quantitative near-orthogonality to a true observed old column under genuine conjugacy and a bounded relative correction.
Use: Complete the actual uniform gated-RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, real recorded and full-window bounds.
Proof: True old-image conjugacy controls the actual normalized line pairing by the real image error. The proved actual unit-step change contributes at most twice the relative correction; add the genuine inner-product estimates.
-/
theorem recorded_step_observed_angle (s y line χ : E) (hs : ‖s‖=1)
    {η q : ℝ} (hy : ‖y-s‖≤η) (ho : inner ℝ y line=0)
    (hline : 0<‖line‖) (hq : q<1) (hχ : ‖χ‖≤q*‖line‖) :
    |inner ℝ s (NormedSpace.normalize (line+χ))|≤η+2*q := by
  have hl : line≠0 := norm_pos_iff.mp hline
  have hyl : inner ℝ y (NormedSpace.normalize line)=0 := by
    rw [NormedSpace.normalize,real_inner_smul_right,ho,mul_zero]
  have hangle := approximate_conjugacy_bound s y (NormedSpace.normalize line)
    (ContinuousLinearMap.id ℝ E) hs (ε := 0) (by simp) hy hyl
  simp only [ContinuousLinearMap.id_apply,zero_add,NormedSpace.norm_normalize hl,mul_one] at hangle
  have hd := recorded_step_normalized_change line χ hline hq hχ
  have hi := norm_inner_le_norm (𝕜 := ℝ) s
    (NormedSpace.normalize (line+χ)-NormedSpace.normalize line)
  rw [Real.norm_eq_abs,hs,one_mul] at hi
  have he : inner ℝ s (NormedSpace.normalize (line+χ))=
      inner ℝ s (NormedSpace.normalize line)+
        inner ℝ s (NormedSpace.normalize (line+χ)-NormedSpace.normalize line) := by
    rw [inner_sub_right]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hangle (hi.trans hd))

end
end krylov.Correction
