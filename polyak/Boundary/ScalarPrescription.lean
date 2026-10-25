import polyak.Regularity.Continuity
import polyak.Regularity.Piecewise
import polyak.Boundary.P2.Physical
import polyak.Boundary.SpiralRegularity
import polyak.Boundary.SpiralEndpoint

/-!
Article: Theorem classification, the unique scalar rate prescription.
Use: continuous actual V and strict derivative bounds on the open arcs give
global monotonicity across their endpoints. The actual attained T solves the equation.
-/
noncomputable section
namespace polyak.Boundary
open Spectral Regularity Set
open Filter
open scoped Topology

def logarithmicCoordinate (t : ℝ) : ℝ := t-V t

theorem logarithmicCoordinate_continuous : Continuous logarithmicCoordinate :=
  continuous_id.sub V_continuous

theorem logarithmicCoordinate_strictMono_of_derivative_bounds
    (hderiv : ∀ t : ℝ,Real.cosh t≠P2.Ga → Real.cosh t≠G1 → Real.cosh t≠GW →
      DifferentiableAt ℝ V t ∧ |deriv V t|<1) : StrictMono logarithmicCoordinate := by
  have ha : 1<P2.Ga := by linarith [P2.Ga_bounds.1]
  have hb : 1<G1 := by linarith [G1_bounds.1]
  have hc : 1<GW := by linarith [GW_bounds.1]
  apply strictMono_of_deriv_pos_away_abs_cuts (Real.arcosh_pos ha)
    ((Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr P2.Ga_lt_G1)
    ((Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr G1_lt_GW)
    logarithmicCoordinate_continuous
  intro t hna hnb hnc
  have hne {G : ℝ} (hn : |t|≠Real.arcosh G) : Real.cosh t≠G := by
    intro he
    apply hn
    calc
      |t|=Real.arcosh (Real.cosh |t|) := (Real.arcosh_cosh (abs_nonneg t)).symm
      _=Real.arcosh G := by rw [Real.cosh_abs,he]
  obtain ⟨hd,habs⟩ := hderiv t (hne hna) (hne hnb) (hne hnc)
  have hF : HasDerivAt logarithmicCoordinate (1-deriv V t) t :=
    (hasDerivAt_id t).sub hd.hasDerivAt
  rw [hF.deriv]
  linarith [(abs_lt.mp habs).2]

theorem scalar_prescription_unique {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hmono : StrictMono logarithmicCoordinate) :
    ∃! t : ℝ,t-V t=Real.log q := by
  have hactual : logarithmicCoordinate (T q)=Real.log q := by
    dsimp [logarithmicCoordinate]
    linarith [T_sub_log_eq_V hq hq1]
  refine ⟨T q,hactual,?_⟩
  intro t ht
  exact hmono.injective (ht.trans hactual.symm)

theorem T_continuousAt_of_coordinate_strictMono {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hmono : StrictMono logarithmicCoordinate) : ContinuousAt T q := by
  have hactual {r : ℝ} (hr : 0<r) (hr1 : r<1) :
      logarithmicCoordinate (T r)=Real.log r := by
    dsimp [logarithmicCoordinate]
    linarith [T_sub_log_eq_V hr hr1]
  have hdom : ∀ᶠ r in 𝓝 q,0<r ∧ r<1 := Ioo_mem_nhds hq hq1
  have hlog := (Real.continuousAt_log (ne_of_gt hq)).tendsto
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hlt : logarithmicCoordinate b<Real.log q := by
      rw [←hactual hq hq1]
      exact hmono hb
    filter_upwards [hdom,hlog.eventually (lt_mem_nhds hlt)] with r hr hl
    exact hmono.lt_iff_lt.mp (by rwa [hactual hr.1 hr.2])
  · intro b hb
    have hlt : Real.log q<logarithmicCoordinate b := by
      rw [←hactual hq hq1]
      exact hmono hb
    filter_upwards [hdom,hlog.eventually (gt_mem_nhds hlt)] with r hr hl
    exact hmono.lt_iff_lt.mp (by rwa [hactual hr.1 hr.2])

end polyak.Boundary
