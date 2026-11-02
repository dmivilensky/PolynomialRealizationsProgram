import krylov.Asymptotics.RecoveryDesign
import krylov.Asymptotics.RecoveryMesh

/-!
Article: main_krylov, thm:limit, matching lower bound.
Use: a fixed inflation c>1 of the exact source spacing produces genuine
spectrally admissible recovery designs. Their scaled rewards converge to
the actual compact continuum reward divided by c. The same candidates fit
every finite cycle with M theta tending to infinity.
Source: the proved physical Gershgorin estimate, genuine energy/reward
convergence, the finite spectral dictionary, and true floor-grid limits.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real Filter MeasureTheory Finset
open krylov.Design krylov.Strings
open scoped Topology BigOperators

/-- A fixed positive inflation of the exact source spacing. -/
def recoveryMesh (I : chebyshev1.SpectralInterval) (c : ℝ) : ℝ := c * designSpacing I

theorem recoveryMesh_pos (I : chebyshev1.SpectralInterval) {c : ℝ} (hc : 0 < c) :
    0 < recoveryMesh I c := mul_pos hc (designSpacing_pos I)

/-- The actual number of edges of the floor recovery grid. -/
def recoveryCount (Y : ℝ) (I : chebyshev1.SpectralInterval) (c : ℝ) : ℕ := ⌊Y / recoveryMesh I c⌋₊

namespace RecoveryState

/-- The genuine spectrally constrained candidate, including its unit origin
mass and all midpoint/right sample choices. -/
def floorString {Y c : ℝ} (R : RecoveryState Y) (hY : 0 < Y)
    (I : chebyshev1.SpectralInterval) (hc : 0 < c) : DiscreteString (recoveryCount Y I c) :=
  R.string (recoveryMesh_pos I hc) (recoveryCount Y I c)
    (floor_mesh_le hY.le (recoveryMesh_pos I hc))

/-- The actual finite power sum of the physical floor-grid string. -/
def floorReward {Y c : ℝ} (R : RecoveryState Y) (hY : 0 < Y)
    (I : chebyshev1.SpectralInterval) (hc : 0 < c) (γ : ℝ) : ℝ :=
  R.discreteReward γ (recoveryMesh_pos I hc) (recoveryCount Y I c)
    (floor_mesh_le hY.le (recoveryMesh_pos I hc))

theorem floorReward_eq_sum {Y c : ℝ} (R : RecoveryState Y) (hY : 0 < Y)
    (I : chebyshev1.SpectralInterval) (hc : 0 < c) (γ : ℝ) :
    R.floorReward hY I hc γ = ∑ j ∈ range (recoveryCount Y I c),
      (R.floorString hY I hc).K (j + 1) ^ (-γ) := rfl

/-- The true source spacing of any diverging physical spectral interval
tends to zero. -/
theorem sourceSpacing_tendsto_zero {ι : Type*} {l : Filter ι}
    {I : ι → chebyshev1.SpectralInterval}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop) :
    Tendsto (fun i ↦ designSpacing (I i)) l (𝓝 0) := by
  simpa only [Function.comp_def, gapSpacing_eq_designSpacing] using gapSpacing_tendsto_zero.comp hR

/-- Actual scaled reward convergence for the genuine finite physical strings. -/
theorem floorReward_scaled_tendsto {ι : Type*} {l : Filter ι} {Y γ c : ℝ}
    (R : RecoveryState Y) (hY : 0 < Y) (hγ : 0 ≤ γ) (hc : 0 < c)
    {I : ι → chebyshev1.SpectralInterval}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop) :
    Tendsto (fun i ↦ designSpacing (I i) * R.floorReward hY (I i) hc γ) l
      (𝓝 ((∫ y in 0..Y, R.energy y ^ (-γ)) / c)) := by
  have hzero : Tendsto (fun i ↦ recoveryMesh (I i) c) l (𝓝 0) := by
    simpa only [recoveryMesh, mul_zero] using (sourceSpacing_tendsto_zero hR).const_mul c
  have hend := floor_mesh_tendsto hY.le
    (Eventually.of_forall (fun i ↦ recoveryMesh_pos (I i) hc)) hzero
  have ht := (R.reward_tendsto hY hγ (fun i ↦ recoveryMesh_pos (I i) hc)
    (fun i ↦ floor_mesh_le hY.le (recoveryMesh_pos (I i) hc)) hzero hend).div_const c
  convert ht using 1
  funext i
  dsimp [floorReward, recoveryCount, recoveryMesh]
  field_simp

/-- Genuine operator-norm admissibility of the actual floor candidates is
a conclusion of compact C¹ density regularity and the physical row bound. -/
theorem floorString_eventually_admissible {ι : Type*} {l : Filter ι} {Y c : ℝ}
    (R : RecoveryState Y) (hY : 0 < Y) (hc : 1 < c)
    {I : ι → chebyshev1.SpectralInterval}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop) :
    ∀ᶠ i in l, (R.floorString hY (I i) (zero_lt_one.trans hc)).spectralRadius ≤ (I i).kappa - 1 := by
  have hlogC1 := R.density_C1.log (fun y hy ↦ (R.density_pos y hy).ne')
  obtain ⟨L, hL, _, hlog⟩ := compact_C1_scalar_bounds hlogC1
  have hzero : Tendsto (fun i ↦ recoveryMesh (I i) c) l (𝓝 0) := by
    simpa only [recoveryMesh, mul_zero] using (sourceSpacing_tendsto_zero hR).const_mul c
  have hz : ∀ᶠ i in l, recoveryMesh (I i) c * R.density 0 ≤ 1 := by
    have ht := hzero.mul_const (R.density 0)
    exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) * R.density 0 < 1))
  have hspec := inflated_mesh_spectral (L := L) hR hc
  filter_upwards [hz, hspec] with i hi hs
  have ht := recovery_spectralRadius_le (recoveryMesh_pos (I i) (zero_lt_one.trans hc))
    (recoveryCount Y (I i) c) (floor_mesh_le hY.le (recoveryMesh_pos (I i) (zero_lt_one.trans hc)))
    R.density_pos hL hi hlog
  change (R.floorString hY (I i) (zero_lt_one.trans hc)).spectralRadius ≤ _ at ht ⊢
  exact ht.trans (by simpa only [recoveryMesh, gapSpacing_eq_designSpacing] using hs)

/-- Every strict lower target below the compact recovery value divided by
c is eventually attained in the original optimized infinite criterion. -/
theorem eventually_lower_infinitePowerValue {ι : Type*} {l : Filter ι} {Y γ c b : ℝ}
    (R : RecoveryState Y) (hY : 0 < Y) (hγ : 0 < γ) (hc : 1 < c)
    {I : ι → chebyshev1.SpectralInterval}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop)
    (hb : b < (∫ y in 0..Y, R.energy y ^ (-γ)) / c) :
    ∀ᶠ i in l, b < designSpacing (I i) * infinitePowerValue (I i) γ := by
  have hlim := R.floorReward_scaled_tendsto hY hγ.le (zero_lt_one.trans hc) hR
  filter_upwards [hlim.eventually (Ioi_mem_nhds hb), R.floorString_eventually_admissible hY hc hR] with i hi hs
  apply hi.trans_le
  apply mul_le_mul_of_nonneg_left _ (designSpacing_pos (I i)).le
  rw [floorReward_eq_sum]
  exact DiscreteString.reward_le_infinitePowerValue _ _ hγ hs

/-- The same genuine candidates fit every finite degree budget satisfying
the source simultaneous growing-memory condition. -/
theorem eventually_lower_optimalValue {ι : Type*} {l : Filter ι} {Y γ c b : ℝ}
    (R : RecoveryState Y) (hY : 0 < Y) (hγ : 0 < γ) (hc : 1 < c)
    {I : ι → chebyshev1.SpectralInterval} {M : ι → ℕ}
    (hR : Tendsto (fun i ↦ (I i).kappa - 1) l atTop)
    (hM : Tendsto (fun i ↦ (M i : ℝ) * designSpacing (I i)) l atTop)
    (hb : b < (∫ y in 0..Y, R.energy y ^ (-γ)) / c) :
    ∀ᶠ i in l, b < designSpacing (I i) * optimalValue (I i) (M i) (fun _ ↦ 1) γ := by
  have hlim := R.floorReward_scaled_tendsto hY hγ.le (zero_lt_one.trans hc) hR
  have hMh : Tendsto (fun i ↦ (M i : ℝ) * recoveryMesh (I i) c) l atTop := by
    simpa only [recoveryMesh, mul_left_comm] using hM.const_mul_atTop (zero_lt_one.trans hc)
  have hfits := floor_mesh_fits (Y := Y)
    (Eventually.of_forall (fun i ↦ recoveryMesh_pos (I i) (zero_lt_one.trans hc))) hMh
  filter_upwards [hlim.eventually (Ioi_mem_nhds hb),
    R.floorString_eventually_admissible hY hc hR, hfits] with i hi hs hf
  apply hi.trans_le
  apply mul_le_mul_of_nonneg_left _ (designSpacing_pos (I i)).le
  rw [floorReward_eq_sum]
  exact DiscreteString.reward_le_optimalValue_of_le _ _ hγ hs hf

end RecoveryState
end
end krylov.Asymptotics
