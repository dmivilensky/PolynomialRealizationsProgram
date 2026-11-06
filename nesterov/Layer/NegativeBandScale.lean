import nesterov.Layer.NegativeBandGeometry

/-! epsilon is negligible against the cubic frequency scale on a layer band. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

private theorem cubic_scale_ratio {ε x : ℝ} (he : 0<ε) (hx : 0<x) :
    ε/Spread.cubicScale x=
      Real.sqrt (Real.sqrt ε)/((x/Real.sqrt ε)*Real.sqrt (x/Real.sqrt ε)) := by
  have hs : 0<Real.sqrt ε := Real.sqrt_pos.mpr he
  have hss : 0<Real.sqrt (Real.sqrt ε) := Real.sqrt_pos.mpr hs
  have hxs : 0<Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [Real.sqrt_div hx.le]
  unfold Spread.cubicScale
  calc
    _=(Real.sqrt ε)^2/(x*Real.sqrt x) := by rw [Real.sq_sqrt he.le]
    _=Real.sqrt (Real.sqrt ε)/((x/Real.sqrt ε)*(Real.sqrt x/Real.sqrt (Real.sqrt ε))) := by
      field_simp
      rw [Real.sq_sqrt hs.le]

theorem layer_epsilon_div_cubic_tendsto {x : A→ℝ} {b : ℝ} (hb : 0<b)
    (hx : Tendsto (fun a=>x a/Real.sqrt (F.epsilon a)) l (𝓝 b)) :
    Tendsto (fun a=>F.epsilon a/Spread.cubicScale (x a)) l (𝓝 0) := by
  have hss : Tendsto (fun a=>Real.sqrt (Real.sqrt (F.epsilon a))) l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using F.sqrt_epsilon_tendsto.sqrt
  have ht := hss.div (hx.mul hx.sqrt) (mul_pos hb (Real.sqrt_pos.mpr hb)).ne'
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [F.epsilon_pos,hx.eventually (eventually_gt_nhds hb)] with a he hx
  have hxp : 0<x a := (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr he)).mp hx
  exact (cubic_scale_ratio he hxp).symm

end
end nesterov.TwoStep.Scaling
