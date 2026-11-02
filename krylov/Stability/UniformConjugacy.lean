import krylov.Methods.ProjectedSearch
import krylov.Methods.CanonicalWindows
import krylov.Methods.ExecutedFC
import krylov.Stability.WeightedNormalization

/-!
Article: main_krylov, apB:lem:UAsteps, exact actual FC normalized angles.
Use: derive step-length-independent near-orthogonality from the real
old-image conjugacy equations and actual canonical operator deviations.
Source: true executed FC conjugacy, the genuine metric pairing and
Cauchy--Schwarz; zero actual steps normalize to zero and are included.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- True operator conjugacy bounds the angle between normalized actual vectors by the genuine operator deviation.
Use: obtains normalized FC angles without any lower bound on either actual vector length.
Article: main_krylov, apB:lem:UAsteps, exact perturbed conjugacy bound.
Proof: zero vectors are immediate. Otherwise normalize both actual vectors,
use the true zero image pairing, and apply the proved approximate-conjugacy
bound with the identity target and the genuine operator image error. -/
theorem normalized_conjugacy_bound (x y : E) (B : E →L[ℝ] E) {η : ℝ}
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤η) (ho : inner ℝ x (B y)=0) :
    |inner ℝ (NormedSpace.normalize x) (NormedSpace.normalize y)|≤η := by
  -- Normalize only after separating zero actual steps; no reciprocal minimum length appears in the bound.
  have hη := (norm_nonneg (B-ContinuousLinearMap.id ℝ E)).trans hB
  by_cases hx : x=0
  · simp only [hx,NormedSpace.normalize_zero_eq_zero,inner_zero_left,abs_zero]
    exact hη
  by_cases hy : y=0
  · simp only [hy,NormedSpace.normalize_zero_eq_zero,inner_zero_right,abs_zero]
    exact hη
  have hu := NormedSpace.norm_normalize hy
  have hv := NormedSpace.norm_normalize hx
  have himage : ‖B (NormedSpace.normalize y)-NormedSpace.normalize y‖≤η := by
    change ‖(B-ContinuousLinearMap.id ℝ E) (NormedSpace.normalize y)‖≤η
    exact ((B-ContinuousLinearMap.id ℝ E).le_opNorm _).trans (by simpa only [hu,mul_one] using hB)
  have horth : inner ℝ (B (NormedSpace.normalize y)) (NormedSpace.normalize x)=0 := by
    rw [real_inner_comm]
    simp only [NormedSpace.normalize,map_smul,real_inner_smul_left,real_inner_smul_right,ho,mul_zero]
  have ht := approximate_conjugacy_bound (NormedSpace.normalize y) (B (NormedSpace.normalize y))
    (NormedSpace.normalize x) (ContinuousLinearMap.id ℝ E) hu
    (ε := 0) (by simp only [sub_self,norm_zero,le_refl]) himage horth
  simpa only [ContinuousLinearMap.id_apply,zero_add,hv,mul_one,real_inner_comm] using ht

/-- The actual full-memory FC normalized canonical steps have angle bounded by the true preceding canonical operator error.
Use: the uniform stability induction starts from a proved exact algorithmic angle estimate.
Article: main_krylov, apB:lem:UAsteps, |τ_iᵀτ_j|≤W.
Proof: the real inverse solve makes each current step orthogonal to the
actual old secant image. The true root pairing transfers that equation to
canonical coordinates; the general normalized conjugacy bound applies. -/
theorem fullFC_canonical_angle {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) {j k : ℕ} (hjk : j<k)
    (hsolve : IsUnit (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det)
    {η : ℝ} (hA : ‖canonicalOperator base (A j)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    |inner ℝ (NormedSpace.normalize (R (fcStep fullMemory A g k)))
      (NormedSpace.normalize (R (fcStep fullMemory A g j)))|≤η := by
  apply normalized_conjugacy_bound _ _ (canonicalOperator base (A j)) hA
  rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
  exact fullFC_step_conjugate A g hjk hsolve

end
end krylov.Stability
