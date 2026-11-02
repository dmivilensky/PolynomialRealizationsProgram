import krylov.Convergence.SS1FModel
import krylov.Functions.CubicSelfConcordant
import krylov.Functions.MidpointQuadratic

/-!
Article: main_krylov, thm:ss1F, original spectral third-variation estimates.
Use: transfer the genuine scalar third differential to the derivative of
the actual vector Hessian, and retain the exact cubic spectral budget in
the newer-secant leading term. Source: the real Riesz isometry, the proved
Banach tensor identity, and the genuine segment midpoint Taylor estimate.
-/

namespace krylov.Convergence
noncomputable section
open Set InnerProductSpace krylov.Functions krylov.Tensor
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance scalarBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] ℝ)
local instance scalarBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] ℝ)
local instance vectorBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] E)
local instance vectorBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=E) (F:=E →L[ℝ] E)

/-- The inverse Riesz map recovers the true vector Hessian from its actual
gradient differential representation. -/
theorem inverseRiesz_gradientHessian (H : E → E →L[ℝ] E) (x : E) :
    inverseRiesz.comp (gradientHessian H x)=H x := by
  ext u
  change (toDual ℝ E).symm ((toDual ℝ E) (H x u))=H x u
  exact (toDual ℝ E).symm_apply_apply _

/-- A genuine scalar third differential is exactly the genuine derivative
of the original vector Hessian after its true Riesz identification. -/
theorem hessian_hasFDerivAt_of_scalar_third
    (H : E → E →L[ℝ] E) (T : SymmetricCubic E) (x : E)
    (hT : HasFDerivAt (gradientHessian H) T.form x) :
    HasFDerivAt H (canonicalVariation T) x := by
  let P : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E inverseRiesz
  have hd : HasFDerivAt (fun z=>P (gradientHessian H z)) (P.comp T.form) x := by
    apply HasFDerivAt.comp x
    · exact P.hasFDerivAt
    · convert! hT
  have he : (fun z=>P (gradientHessian H z))=H := funext fun z=>inverseRiesz_gradientHessian H z
  rw [he] at hd
  exact hd

/-- A true scalar mixed budget controls the Riesz vector action with the
same constant; no polarization or dimension factor is lost. -/
theorem canonicalVariation_action_bound (T : SymmetricCubic E) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ u v w,|T.form u v w|≤B*‖u‖*‖v‖*‖w‖) (u v : E) :
    ‖canonicalVariation T u v‖≤B*‖u‖*‖v‖ := by
  let w := canonicalVariation T u v
  have hh := hbound u w v
  rw [←canonicalVariation_pair T u w v,real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hh
  change ‖w‖≤B*‖u‖*‖v‖
  by_cases hw : w=0
  · rw [hw,norm_zero]; positivity
  · have hp : 0<‖w‖ := norm_pos_iff.mpr hw
    nlinarith only [hh,hp]

/-- Original spectral Lipschitz third derivatives give the true vector
Hessian derivative's operator Lipschitz bound with the same constant. -/
theorem canonicalVariation_lipschitz_of_spectral [FiniteDimensional ℝ E]
    (T : E → SymmetricCubic E) (S : Set E) (L : ℝ≥0)
    (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖) :
    LipschitzOnWith L (fun z=>canonicalVariation (T z)) S := by
  have hm := thirdVariationLipschitzOn_of_diagonal T L S hLip
  have hresult : LipschitzOnWith (Real.toNNReal (L:ℝ)) (fun z=>canonicalVariation (T z)) S := by
    apply LipschitzOnWith.of_dist_le'
    intro p hp q hq
    rw [dist_eq_norm,dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    let w := canonicalVariation (T p) u v-canonicalVariation (T q) u v
    have hh := hm p hp q hq u w v
    have he : (T p).form u w v-(T q).form u w v=‖w‖^2 := by
      rw [←canonicalVariation_pair (T p) u w v,←canonicalVariation_pair (T q) u w v,
        ←inner_sub_right,real_inner_self_eq_norm_sq]
    rw [he,abs_of_nonneg (sq_nonneg _)] at hh
    change ‖w‖≤(L:ℝ)*‖p-q‖*‖u‖*‖v‖
    by_cases hw : w=0
    · rw [hw,norm_zero]; positivity
    · have hwpos : 0<‖w‖ := norm_pos_iff.mpr hw
      nlinarith only [hh,hwpos]
  simpa only [Real.toNNReal_coe] using hresult

/-- The true vector third-variation norm bounds every actual unit
diagonal; this supplies the original T3 without an extra budget premise. -/
theorem canonicalVariation_unit_diagonal_bound (T : SymmetricCubic E) (h : E) (hh : ‖h‖=1) :
    |T.form h h h|≤‖canonicalVariation T‖ := by
  rw [←canonicalVariation_pair T h h h]
  have hv := (canonicalVariation T h).le_opNorm h
  have ho := (canonicalVariation T).le_opNorm h
  rw [hh,mul_one] at hv ho
  have hp := norm_inner_le_norm (𝕜:=ℝ) h (canonicalVariation T h h)
  simpa only [Real.norm_eq_abs,hh,one_mul] using hp.trans
    (mul_le_mul_of_nonneg_left (hv.trans ho) (norm_nonneg h))

/-- The actual vector derivative norm equals the original diagonal tensor
spectral budget in its exact bound characterization. -/
theorem canonicalVariation_norm_le_iff_spectral [FiniteDimensional ℝ E]
    (T : SymmetricCubic E) {B : ℝ} (hB : 0≤B) :
    ‖canonicalVariation T‖≤B ↔∀ h:E,‖h‖=1 → |T.form h h h|≤B := by
  constructor
  · intro hn h hh
    exact (canonicalVariation_unit_diagonal_bound T h hh).trans hn
  · intro hb
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg _))
    intro v
    exact canonicalVariation_action_bound T hB (cubic_diagonal_bound T B hb) u v

/-- The original C3,1 spectral hypothesis itself supplies the local
Hessian Lipschitz constant on a bounded convex domain. -/
theorem hessian_lipschitz_of_scalar_third [FiniteDimensional ℝ E]
    (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E) (S : Set E)
    (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (L : ℝ≥0) (hLip : ∀ p∈S,∀ q∈S,∀ h:E,‖h‖=1 →
      |(T p).form h h h-(T q).form h h h|≤(L:ℝ)*‖p-q‖)
    {R : ℝ} (hR : 0≤R) (hbound : ∀ z∈S,‖z‖≤R) :
    LipschitzOnWith (Real.toNNReal (‖canonicalVariation (T 0)‖+(L:ℝ)*R)) H S := by
  have hD := canonicalVariation_lipschitz_of_spectral T S L hLip
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz=>(hessian_hasFDerivAt_of_scalar_third H (T z) z (hT z hz)).hasFDerivWithinAt) _ hS
  intro z hz
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by positivity)]
  change ‖canonicalVariation (T z)‖≤‖canonicalVariation (T 0)‖+(L:ℝ)*R
  have hh := hD.norm_sub_le hz h₀
  rw [sub_zero] at hh
  have he : canonicalVariation (T z)=
      (canonicalVariation (T z)-canonicalVariation (T 0))+canonicalVariation (T 0) := by abel
  calc
    _ = ‖(canonicalVariation (T z)-canonicalVariation (T 0))+canonicalVariation (T 0)‖ := congrArg norm he
    _ ≤ ‖canonicalVariation (T z)-canonicalVariation (T 0)‖+‖canonicalVariation (T 0)‖ := by
      convert! norm_add_le (canonicalVariation (T z)-canonicalVariation (T 0)) (canonicalVariation (T 0))
    _ ≤ (L:ℝ)*R+‖canonicalVariation (T 0)‖ := add_le_add
      (hh.trans (mul_le_mul_of_nonneg_left (hbound z hz) L.coe_nonneg)) le_rfl
    _ = _ := add_comm _ _

/-- A genuine bounded continuous third differential supplies the local
Hessian Lipschitz constant without any Lipschitz-third hypothesis. -/
theorem hessian_lipschitz_of_third_spectral_bound [FiniteDimensional ℝ E]
    (H : E → E →L[ℝ] E) (T : E → SymmetricCubic E) (S : Set E)
    (hS : Convex ℝ S) (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    {B : ℝ} (hB : 0≤B) (hbudget : ∀ z∈S,∀ h:E,‖h‖=1 → |(T z).form h h h|≤B) :
    LipschitzOnWith (Real.toNNReal B) H S := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z hz=>(hessian_hasFDerivAt_of_scalar_third H (T z) z (hT z hz)).hasFDerivWithinAt) _ hS
  intro z hz
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ hB]
  exact (canonicalVariation_norm_le_iff_spectral (T z) hB).mpr (hbudget z hz)

end
end krylov.Convergence
