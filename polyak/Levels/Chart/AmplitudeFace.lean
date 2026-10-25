import polyak.Levels.Chart.GapPolynomial
import polyak.Levels.Chart.EndpointFaces

/-! The amplitude floor is the +1 coefficient face; convergence to it
forces divergence of the original condition number. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set Filter Topology

theorem amplitude_floor_iff_endpoint {a r₁ r₂ : ℝ} (h₁ : r₁<1) (h₂ : r₂<1) :
    a=amplitudeFloor r₁ r₂ ↔ (gapPolynomial a r₁ r₂).eval 1=0 := by
  rw [gapPolynomial_one]
  unfold amplitudeFloor
  have hn : (1-r₁)*(1-r₂)≠0 :=
    ne_of_gt (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂))
  rw [eq_div_iff hn]
  constructor <;> intro h <;> linarith

theorem kappa_tendsto_of_coefficients {ι : Type*} {l : Filter ι} [NeBot l]
    (q : ι→Tuning) {C : Coefficients}
    (hc : Tendsto (fun i=>coefficients (q i)) l (𝓝 C)) (hplus : C.eval 1=0) :
    Tendsto (fun i=>(q i).kappa) l atTop := by
  have hp : Tendsto (fun i=>(q i).Xi 1) l (𝓝 0) := by
    simpa only [Function.comp_def,eval_coefficients,hplus] using (Coefficients.continuous_eval 1).continuousAt.tendsto.comp hc
  have hm : Tendsto (fun i=>(q i).Xi (-1)) l (𝓝 (C.eval (-1))) := by
    simpa only [Function.comp_def,eval_coefficients] using (Coefficients.continuous_eval (-1)).continuousAt.tendsto.comp hc
  exact kappa_tendsto_atTop_of_endpoint_face q hp hm

 theorem stability_gap_tendsto_of_coefficients {ι : Type*} {l : Filter ι}
    (q : ι→Tuning) {C : Coefficients}
    (hc : Tendsto (fun i=>coefficients (q i)) l (𝓝 C)) (hminus : C.eval (-1)=0) :
    Tendsto (fun i=>2*(1+(q i).beta)-(q i).y) l (𝓝 0) := by
  apply stability_gap_tendsto_zero_of_endpoint_face q
  simpa only [Function.comp_def,eval_coefficients,hminus] using
    (Coefficients.continuous_eval (-1)).continuousAt.tendsto.comp hc

end polyak.Levels.Chart
