import polyak.GapEdges.Junction.Curvature
import polyak.GapEdges.Specialization.Curvature

/-! The junction formula is linked to the literal edge symbol in its
small-slope strip, where these two lags are genuinely adjacent. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels Set Filter
open scoped Topology

theorem junction_source_curvature (q : Tuning) {k : ℕ} (hk : 4≤k) {a t₂ : ℝ}
    (hd : t₂<Real.cos (2*(Real.pi/k)))
    (ha : junctionLower (Real.cos (2*(Real.pi/k))) t₂<a)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    deriv^[2] (firstEdgeSymbol q k) (2*Real.pi/k) =
      Real.sin (Real.pi/k)*deriv^[2] (Geometry.shiftedAngle q 0) (2*Real.pi/k)-
        ((k:ℝ)-2*junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k))*
          junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k)*Real.cos (Real.pi/k) := by
  have hkr : (4:ℝ)≤k := by exact_mod_cast hk
  have hkp : (0:ℝ)<k := by linarith
  have hc : Real.pi/k∈Ioo (0:ℝ) (Real.pi/2) := by
    constructor
    · positivity
    · exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
  have hω : 2*Real.pi/k∈Ioo (0:ℝ) Real.pi := by
    rw [show 2*Real.pi/k=2*(Real.pi/k) by ring]
    constructor <;> linarith [hc.1,hc.2]
  have hzero : FareyPlateau.Edge.shift q k (2*Real.pi/k)=0 := by
    have hh := (junction_cotangent_jets q hc hXi).1
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring] at hh
    unfold FareyPlateau.Edge.shift
    rw [hh]
    ring
  have he : firstEdgePhase q k =ᶠ[𝓝 (2*Real.pi/k)] Geometry.shiftedAngle q 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    unfold firstEdgePhase ModeLocking.TwoLag.phase
    rw [hzero,Geometry.jointAngle_actual q 0 ⟨hx.1.le,hx.2.le⟩]
  have hj := junction_angle_jets q hc hXi
  rw [show 2*(Real.pi/k)=2*Real.pi/k by ring] at hj
  have hchi : firstChi q k= -junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) := by
    unfold firstChi junctionG
    rw [he.deriv_eq]
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    linear_combination hj.2.1
  have ht1 : Real.cos (2*(Real.pi/k))<1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0:ℝ)≤0 by rfl) (by nlinarith [hc.2] : 2*(Real.pi/k)≤Real.pi)
      (by nlinarith [hc.1] : 0<2*(Real.pi/k))
  have hs : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hap : 0<a := lt_trans (show 0<junctionLower (Real.cos (2*(Real.pi/k))) t₂ from
    div_pos (by norm_num) (mul_pos (by linarith) (by linarith))) ha
  have hg : 0<junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) := by
    unfold junctionG
    positivity
  rw [first_edge_curvature q (by omega),hchi,abs_neg,abs_of_pos hg]
  rw [show deriv^[2] (firstEdgePhase q k) (2*Real.pi/k)=
    deriv^[2] (Geometry.shiftedAngle q 0) (2*Real.pi/k) from he.deriv.deriv_eq]

theorem junction_interval_edge_negative (q : Tuning) {k : ℕ} (hk : 4≤k) {a t₂ : ℝ}
    (hd : t₂<Real.cos (2*(Real.pi/k)))
    (ha : a∈Ioo (junctionLower (Real.cos (2*(Real.pi/k))) t₂)
      (junctionUpper k (Real.cos (2*(Real.pi/k))) t₂ (Real.sin (Real.pi/k))))
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    deriv^[2] (firstEdgeSymbol q k) (2*Real.pi/k)<0 ∧
      0<junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) ∧
      junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k)<(k:ℝ)/2 := by
  have hkr : (4:ℝ)≤k := by exact_mod_cast hk
  have hkp : (0:ℝ)<k := by linarith
  have hc : Real.pi/k∈Ioo (0:ℝ) (Real.pi/2) :=
    ⟨by positivity,div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)⟩
  have ht0 : 0≤Real.cos (2*(Real.pi/k)) := by
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    exact (junction_trig_bounds hkr).1
  have ht1 : Real.cos (2*(Real.pi/k))<1 := by
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    exact (junction_trig_bounds hkr).2.1
  have hs : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hb := junction_interval_g_bounds hkr ht0 ht1 hd hs ha.1 ha.2
  refine ⟨?_,hb⟩
  rw [junction_source_curvature q hk hd ha.1 hXi,
    show 2*Real.pi/k=2*(Real.pi/k) by ring]
  exact (junction_small_curvature_negative_iff q hc hd ha.1 hXi).mpr ha

end polyak.GapEdges.Junction
