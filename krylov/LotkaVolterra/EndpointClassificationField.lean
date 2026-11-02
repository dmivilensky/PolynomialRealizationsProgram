import krylov.LotkaVolterra.GlobalEndpointOrbit
import krylov.LotkaVolterra.GlobalFlowEstimate

/-!
Article: `main_krylov`, `apC:prop:g1`, bounded shooting coordinates for all
endpoint initial values. With `q=(s-U)/U` and `U` as independent variable,
the physical nonescape corridor is `1/U < q ≤ 3`. Clipping that coordinate
produces a bounded global scalar flow without changing the field inside
that corridor. Source: exact division of the endpoint LV equations.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

def endpointRatioRate (U q : ℝ) : ℝ := (U * q - 3) / (U * q + 1) * ((1 + q) / U)
def endpointRatioClip (q : ℝ) : ℝ := max 0 (min q 4)
def clippedEndpointRatioRate (U q : ℝ) : ℝ :=
  endpointRatioRate (max 1 U) (endpointRatioClip q)

theorem endpointRatioClip_mem (q : ℝ) : endpointRatioClip q ∈ Icc (0 : ℝ) 4 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem endpointRatioClip_eq {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 4) : endpointRatioClip q = q := by
  simp [endpointRatioClip, min_eq_left hq.2, max_eq_right hq.1]

theorem endpointRatioClip_lipschitz : LipschitzWith 1 endpointRatioClip :=
  (LipschitzWith.id.min_const 4).const_max 0

theorem endpointRatioRate_hasDerivAt {U q : ℝ} (hU : U ≠ 0) (hden : U * q + 1 ≠ 0) :
    HasDerivAt (endpointRatioRate U)
      (4 * (1 + q) / (U * q + 1) ^ 2 + (U * q - 3) / (U * (U * q + 1))) q := by
  have hh := ((((hasDerivAt_id q).const_mul U).sub_const 3).div
    (((hasDerivAt_id q).const_mul U).add_const 1) hden).mul
      (((hasDerivAt_id q).const_add 1).div_const U)
  convert hh using 1
  · rfl
  · dsimp
    field_simp [hU, hden]
    ring

theorem endpointRatioRate_bounds {U q : ℝ} (hU : 1 ≤ U) (hq : q ∈ Icc (0 : ℝ) 4) :
    ‖endpointRatioRate U q‖ ≤ 15 ∧
      ‖4 * (1 + q) / (U * q + 1) ^ 2 + (U * q - 3) / (U * (U * q + 1))‖ ≤ 23 := by
  have hUp : 0 < U := by linarith
  have he : 0 ≤ U * q := mul_nonneg hUp.le hq.1
  have hd : 1 ≤ U * q + 1 := by linarith
  have hdp : 0 < U * q + 1 := by linarith
  have hrat : -3 ≤ (U * q - 3) / (U * q + 1) := by
    apply (le_div_iff₀ hdp).mpr
    linarith
  have hrat' : (U * q - 3) / (U * q + 1) ≤ 1 := by
    apply (div_le_iff₀ hdp).mpr
    linarith
  have hratabs : |(U * q - 3) / (U * q + 1)| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  have hfac : 0 ≤ (1 + q) / U := div_nonneg (by linarith [hq.1]) hUp.le
  have hfac' : (1 + q) / U ≤ 5 := by
    apply (div_le_iff₀ hUp).mpr
    linarith [hq.2]
  constructor
  · change |(U * q - 3) / (U * q + 1) * ((1 + q) / U)| ≤ 15
    rw [abs_mul, abs_of_nonneg hfac]
    nlinarith
  · have hD : 0 ≤ 4 * (1 + q) / (U * q + 1) ^ 2 :=
      div_nonneg (by linarith [hq.1]) (sq_nonneg _)
    have hD' : 4 * (1 + q) / (U * q + 1) ^ 2 ≤ 20 := by
      apply (div_le_iff₀ (sq_pos_of_pos hdp)).mpr
      nlinarith [hq.2]
    have heq : (U * q - 3) / (U * (U * q + 1)) =
        ((U * q - 3) / (U * q + 1)) / U := by rw [div_div]; congr 1; ring
    rw [heq]
    have hlast : -3 ≤ ((U * q - 3) / (U * q + 1)) / U := by
      apply (le_div_iff₀ hUp).mpr
      linarith
    have hlast' : ((U * q - 3) / (U * q + 1)) / U ≤ 1 := by
      apply (div_le_iff₀ hUp).mpr
      linarith
    change |4 * (1 + q) / (U * q + 1) ^ 2 + ((U * q - 3) / (U * q + 1)) / U| ≤ 23
    rw [abs_le]
    constructor <;> linarith

theorem endpointRatioRate_lipschitz {U : ℝ} (hU : 1 ≤ U) :
    LipschitzOnWith 23 (endpointRatioRate U) (Icc (0 : ℝ) 4) := by
  apply (convex_Icc (0 : ℝ) 4).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun q hq ↦ (endpointRatioRate_hasDerivAt (by linarith : U ≠ 0)
      (by nlinarith [hq.1] : U * q + 1 ≠ 0)).hasDerivWithinAt)
  intro q hq
  exact_mod_cast (endpointRatioRate_bounds hU hq).2

theorem clippedEndpointRatioRate_eq {U q : ℝ} (hU : 1 ≤ U) (hq : q ∈ Icc (0 : ℝ) 4) :
    clippedEndpointRatioRate U q = endpointRatioRate U q := by
  simp [clippedEndpointRatioRate, max_eq_right hU, endpointRatioClip_eq hq]

theorem clippedEndpointRatioRate_lipschitz (U : ℝ) :
    LipschitzWith 23 (clippedEndpointRatioRate U) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  calc
    dist (clippedEndpointRatioRate U q) (clippedEndpointRatioRate U r) ≤
        23 * dist (endpointRatioClip q) (endpointRatioClip r) :=
      (endpointRatioRate_lipschitz (le_max_left 1 U)).dist_le_mul
        _ (endpointRatioClip_mem q) _ (endpointRatioClip_mem r)
    _ ≤ 23 * dist q r := by
      gcongr
      simpa using endpointRatioClip_lipschitz.dist_le_mul q r

theorem clippedEndpointRatioRate_continuous_time (q : ℝ) :
    Continuous (clippedEndpointRatioRate · q) := by
  unfold clippedEndpointRatioRate endpointRatioRate
  apply Continuous.mul
  · exact ((continuous_const.max continuous_id |>.mul continuous_const).sub continuous_const).div
      ((continuous_const.max continuous_id |>.mul continuous_const).add continuous_const) (fun U ↦ by
        have hh := (endpointRatioClip_mem q).1
        have hp : 0 ≤ max 1 U * endpointRatioClip q :=
          mul_nonneg (by linarith [le_max_left 1 U]) hh
        linarith)
  · exact continuous_const.div (continuous_const.max continuous_id)
      (fun U ↦ by linarith [le_max_left 1 U])

theorem exists_global_endpoint_ratio_at (U₀ q₀ : ℝ) :
    ∃ q : ℝ → ℝ, q U₀ = q₀ ∧
      ∀ U, HasDerivAt q (clippedEndpointRatioRate U (q U)) U :=
  exists_global_solution_at_of_bounded_lipschitz (L := 15) (K := 23)
    clippedEndpointRatioRate_lipschitz clippedEndpointRatioRate_continuous_time
    (fun U q ↦ (endpointRatioRate_bounds (le_max_left 1 U) (endpointRatioClip_mem q)).1) U₀ q₀

/-- Complete auxiliary flow based at `U=1`. -/
def endpointRatioFlow (ξ : ℝ) : ℝ → ℝ := (exists_global_endpoint_ratio_at 1 ξ).choose

theorem endpointRatioFlow_initial (ξ : ℝ) : endpointRatioFlow ξ 1 = ξ :=
  (exists_global_endpoint_ratio_at 1 ξ).choose_spec.1

theorem endpointRatioFlow_hasDerivAt (ξ U : ℝ) : HasDerivAt (endpointRatioFlow ξ)
    (clippedEndpointRatioRate U (endpointRatioFlow ξ U)) U :=
  (exists_global_endpoint_ratio_at 1 ξ).choose_spec.2 U

end
end krylov.LotkaVolterra
