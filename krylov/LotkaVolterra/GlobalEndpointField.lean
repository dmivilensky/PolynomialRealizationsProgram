import krylov.LotkaVolterra.GlobalBoundedODE
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
Article: `main_krylov`, `apC:prop:g1`.

The scalar equation for the endpoint graph gap `e = s - U`, with `U` as
independent variable. Clipping outside the physical strip produces a bounded
globally Lipschitz equation and therefore genuine global integral curves.
Clipping changes nothing on `U ≥ 1`, `1 ≤ e ≤ 3`.

Source: divide the two exact endpoint equations of `OrbitEstimates`; global
existence is Picard--Lindelöf through `GlobalBoundedODE`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

/-- Gap vector field, written to make its derivative and growth transparent. -/
def endpointGraphRate (U e : ℝ) : ℝ :=
  (e - 3) / (e + 1) + (2 * e - 4 + 4 / (e + 1)) / U

theorem endpointGraphRate_eq {U e : ℝ} (hU : U ≠ 0) (he : e + 1 ≠ 0) :
    endpointGraphRate U e = (U * (e - 3) + 2 * e * (e - 1)) / (U * (e + 1)) := by
  unfold endpointGraphRate
  field_simp
  ring

/-- Projection onto the compact gap strip. -/
def endpointGapClip (e : ℝ) : ℝ := max 1 (min e 3)

theorem endpointGapClip_mem (e : ℝ) : endpointGapClip e ∈ Icc (1 : ℝ) 3 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem endpointGapClip_eq {e : ℝ} (he : e ∈ Icc (1 : ℝ) 3) :
    endpointGapClip e = e := by simp [endpointGapClip, min_eq_left he.2, max_eq_right he.1]

theorem lipschitz_endpointGapClip : LipschitzWith 1 endpointGapClip :=
  (LipschitzWith.id.min_const 3).const_max 1

theorem endpointGraphRate_hasDerivAt {U e : ℝ} (he : e + 1 ≠ 0) :
    HasDerivAt (endpointGraphRate U)
      (4 / (e + 1) ^ 2 + (2 - 4 / (e + 1) ^ 2) / U) e := by
  have h₁ := ((hasDerivAt_id e).sub_const 3).div ((hasDerivAt_id e).add_const 1) he
  have h₂ := (((hasDerivAt_id e).const_mul 2).sub_const 4).add
    ((hasDerivAt_const e 4).div ((hasDerivAt_id e).add_const 1) he)
  convert h₁.add (h₂.div_const U) using 1
  · rfl
  · dsimp
    ring

theorem endpointGraphRate_lipschitz {U : ℝ} (hU : 1 ≤ U) :
    LipschitzOnWith 3 (endpointGraphRate U) (Icc (1 : ℝ) 3) := by
  have hd (e : ℝ) (he : e ∈ Icc (1 : ℝ) 3) :=
    endpointGraphRate_hasDerivAt (U := U) (e := e) (by linarith [he.1])
  apply (convex_Icc (1 : ℝ) 3).lipschitzOnWith_of_nnnorm_deriv_le
    (fun e he ↦ (hd e he).differentiableAt)
  intro e he
  rw [(hd e he).deriv]
  change |4 / (e + 1) ^ 2 + (2 - 4 / (e + 1) ^ 2) / U| ≤ (3 : ℝ)
  have hp : 0 < (e + 1) ^ 2 := sq_pos_of_pos (by linarith [he.1])
  have hq : 0 ≤ 4 / (e + 1) ^ 2 := div_nonneg (by norm_num) hp.le
  have hq₁ : 4 / (e + 1) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [he.1]
  have h₂ : 0 ≤ (2 - 4 / (e + 1) ^ 2) / U :=
    div_nonneg (by linarith) (by linarith)
  have h₂' : (2 - 4 / (e + 1) ^ 2) / U ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < U)).mpr
    linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem endpointGraphRate_norm_le {U e : ℝ} (hU : 1 ≤ U)
    (he : e ∈ Icc (1 : ℝ) 3) : ‖endpointGraphRate U e‖ ≤ 6 := by
  have hp : 0 < e + 1 := by linarith [he.1]
  have hB : 2 * e - 4 + 4 / (e + 1) = 2 * e * (e - 1) / (e + 1) := by
    field_simp
    ring
  have ha : -1 ≤ (e - 3) / (e + 1) := by
    apply (le_div_iff₀ hp).mpr
    linarith [he.1]
  have ha' : (e - 3) / (e + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith [he.2]) hp.le
  have hb : 0 ≤ 2 * e * (e - 1) / (e + 1) := by
    exact div_nonneg (mul_nonneg (by linarith [he.1]) (by linarith [he.1])) hp.le
  have hb' : 2 * e * (e - 1) / (e + 1) ≤ 6 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg (show 0 ≤ 3 - e by linarith [he.2])
      (show 0 ≤ 2 * e by linarith [he.1])]
  have hc : 0 ≤ (2 * e * (e - 1) / (e + 1)) / U := by positivity
  have hc' : (2 * e * (e - 1) / (e + 1)) / U ≤ 6 := by
    apply (div_le_iff₀ (by linarith : 0 < U)).mpr
    linarith
  change |endpointGraphRate U e| ≤ 6
  rw [endpointGraphRate, hB, abs_le]
  constructor <;> linarith

/-- Bounded extension of the graph equation. It agrees with the original
equation everywhere in the relevant positive strip. -/
def clippedEndpointGraphRate (U e : ℝ) : ℝ :=
  endpointGraphRate (max 1 U) (endpointGapClip e)

theorem clippedEndpointGraphRate_eq {U e : ℝ} (hU : 1 ≤ U)
    (he : e ∈ Icc (1 : ℝ) 3) :
    clippedEndpointGraphRate U e = endpointGraphRate U e := by
  simp [clippedEndpointGraphRate, max_eq_right hU, endpointGapClip_eq he]

theorem clippedEndpointGraphRate_lipschitz (U : ℝ) :
    LipschitzWith 3 (clippedEndpointGraphRate U) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro e f
  calc
    dist (clippedEndpointGraphRate U e) (clippedEndpointGraphRate U f) ≤
        3 * dist (endpointGapClip e) (endpointGapClip f) :=
      (endpointGraphRate_lipschitz (le_max_left 1 U)).dist_le_mul
        _ (endpointGapClip_mem e) _ (endpointGapClip_mem f)
    _ ≤ 3 * dist e f := by
      gcongr
      simpa using lipschitz_endpointGapClip.dist_le_mul e f

theorem clippedEndpointGraphRate_continuous_time (e : ℝ) :
    Continuous (clippedEndpointGraphRate · e) := by
  unfold clippedEndpointGraphRate endpointGraphRate
  apply Continuous.add continuous_const
  exact continuous_const.div (continuous_const.max continuous_id)
    (fun U ↦ ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left 1 U)))

theorem clippedEndpointGraphRate_norm_le (U e : ℝ) :
    ‖clippedEndpointGraphRate U e‖ ≤ 6 :=
  endpointGraphRate_norm_le (le_max_left _ _) (endpointGapClip_mem e)

/-- The clipped endpoint equation has a genuine integral curve for every
initial gap, on the whole real `U` axis. -/
theorem exists_global_endpoint_gap (e₀ : ℝ) :
    ∃ e : ℝ → ℝ, e 0 = e₀ ∧
      ∀ U, HasDerivAt e (clippedEndpointGraphRate U (e U)) U :=
  exists_global_solution_of_bounded_lipschitz (L := 6) (K := 3)
    clippedEndpointGraphRate_lipschitz
    clippedEndpointGraphRate_continuous_time clippedEndpointGraphRate_norm_le e₀

end
end krylov.LotkaVolterra
