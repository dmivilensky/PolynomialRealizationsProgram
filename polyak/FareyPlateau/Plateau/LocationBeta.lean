import polyak.FareyPlateau.Plateau.LocationLimit

/-! The momentum limit and the exact scaling law. -/
noncomputable section
namespace polyak.FareyPlateau
open Levels Filter Set Topology

theorem edgeRoot_normalizedB (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) :
    Chart.normalizedB C=1/shiftedEdgeRoot C a := by
  unfold Chart.normalizedB shiftedEdgeRoot
  rw [he]
  congr 1
  dsimp [edgeCoefficients]
  ring

theorem edgeRoot_normalizedU (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) :
    (Chart.normalizedU C)^2*shiftedEdgeRoot C a=2*a+shiftedEdgeRoot C a := by
  rw [Chart.normalizedU_sq,edgeRoot_normalizedB C he]
  field_simp [(shiftedEdgeRoot_pos C he).ne']
  unfold shiftedEdgeRoot
  ring

theorem edgeRoot_scale (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) :
    a*(1-Chart.inverseBeta C)^2=2*Chart.inverseBeta C*shiftedEdgeRoot C a := by
  have hu := edgeRoot_normalizedU C he
  have hpos := Chart.one_lt_normalizedU C
  have hr := shiftedEdgeRoot_pos C he
  unfold Chart.inverseBeta
  field_simp [show Chart.normalizedU C+1≠0 by linarith]
  nlinarith [hu]

theorem normalizedU_edge_atTop {ι : Type*} {l : Filter ι}
    (C : ι→Chart.CoefficientPoint) (a : ι→ℝ) {c h D : ℝ}
    (he : ∀i,(C i).val=edgeCoefficients c h (a i) D)
    (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) (ha : Tendsto a l atTop) :
    Tendsto (fun i=>Chart.normalizedU (C i)) l atTop := by
  have hbound (i) : 4*h*a i≤(Chart.normalizedU (C i))^2 := by
    have hu := edgeRoot_normalizedU (C i) (he i)
    have hb := shiftedEdgeRoot_bound (C i) (he i) hc hh
    rw [le_div_iff₀ (by positivity : 0<2*h)] at hb
    have hr := shiftedEdgeRoot_pos (C i) (he i)
    have hp := mul_nonneg (show 0≤1-2*h*shiftedEdgeRoot (C i) (a i) by nlinarith)
      (sq_nonneg (Chart.normalizedU (C i)))
    nlinarith [hu]
  have hsq : Tendsto (fun i=>(Chart.normalizedU (C i))^2) l atTop :=
    tendsto_atTop_mono hbound (ha.const_mul_atTop (by positivity))
  have ht := Real.tendsto_sqrt_atTop.comp hsq
  have heq : (fun i=>Real.sqrt ((Chart.normalizedU (C i))^2))=
      (fun i=>Chart.normalizedU (C i)) := by
    funext i
    exact Real.sqrt_sq (by linarith [Chart.one_lt_normalizedU (C i)])
  simpa only [Function.comp_def,heq] using ht

theorem inverseBeta_edge_tendsto {ι : Type*} {l : Filter ι}
    (C : ι→Chart.CoefficientPoint) (a : ι→ℝ) {c h D : ℝ}
    (he : ∀i,(C i).val=edgeCoefficients c h (a i) D)
    (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) (ha : Tendsto a l atTop) :
    Tendsto (fun i=>Chart.inverseBeta (C i)) l (𝓝 1) := by
  have hu := normalizedU_edge_atTop C a he hc hh ha
  have hden := tendsto_atTop_add_const_right l 1 hu
  have ht := hden.const_div_atTop (2:ℝ)
  have hlim : Tendsto (fun i=>1-2/(Chart.normalizedU (C i)+1)) l (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub ht
  convert hlim using 1
  funext i
  unfold Chart.inverseBeta
  field_simp [show Chart.normalizedU (C i)+1≠0 by linarith [Chart.one_lt_normalizedU (C i)]]
  ring

theorem scale_edge_tendsto {ι : Type*} {l : Filter ι}
    (C : ι→Chart.CoefficientPoint) (a : ι→ℝ) {c h D : ℝ}
    (he : ∀i,(C i).val=edgeCoefficients c h (a i) D)
    (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) (ha : Tendsto a l atTop) :
    Tendsto (fun i=>a i*(1-Chart.inverseBeta (C i))^2) l (𝓝 (2*edgeRootLimit c h)) := by
  have ht := ((inverseBeta_edge_tendsto C a he hc hh ha).const_mul 2).mul
    (shiftedEdgeRoot_tendsto C a he hc hh ha)
  simpa only [mul_one,←edgeRoot_scale _ (he _)] using ht

end polyak.FareyPlateau
