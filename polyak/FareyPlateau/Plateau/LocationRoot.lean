import polyak.FareyPlateau.Domain.Gap

/-! A stable secular-root formula for the large-curvature limit.  The
shifted root is positive, uniformly bounded, and tends to an explicit
quadratic root.  This avoids choosing subsequential limits of tunings. -/
noncomputable section
namespace polyak.FareyPlateau
open Levels Filter Set Topology

def shiftedEdgeRoot (C : Chart.CoefficientPoint) (a : ℝ) : ℝ := Chart.stableRoot C-2*a

theorem shiftedEdgeRoot_pos (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) : 0<shiftedEdgeRoot C a := by
  have hs := (Chart.stableRoot_spec C).1
  rw [he] at hs
  change -2*(-a)<Chart.stableRoot C at hs
  unfold shiftedEdgeRoot
  linarith

theorem shiftedEdgeRoot_equation (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) :
    (1-c^2)*shiftedEdgeRoot C a+2*h+
      (1+D-c*shiftedEdgeRoot C a)^2/(2*a+shiftedEdgeRoot C a)-
      1/shiftedEdgeRoot C a=0 := by
  have hs := (Chart.stableRoot_spec C).2.2
  rw [he] at hs
  dsimp [Chart.secular,edgeCoefficients] at hs
  have hr := shiftedEdgeRoot_pos C he
  have hd := Chart.stableRoot_pos C
  unfold shiftedEdgeRoot at hr ⊢
  field_simp [ne_of_gt hr,ne_of_gt hd] at hs ⊢
  nlinarith [hs]

theorem shiftedEdgeRoot_identity (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) :
    (1-c^2)*(shiftedEdgeRoot C a)^2+2*h*shiftedEdgeRoot C a+
      shiftedEdgeRoot C a*(1+D-c*shiftedEdgeRoot C a)^2/
        (2*a+shiftedEdgeRoot C a)=1 := by
  have heq := congrArg (fun x : ℝ=>x*shiftedEdgeRoot C a) (shiftedEdgeRoot_equation C he)
  rw [sub_mul,div_mul_cancel₀ _ (shiftedEdgeRoot_pos C he).ne'] at heq
  linear_combination heq

theorem shiftedEdgeRoot_bound (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) :
    shiftedEdgeRoot C a≤1/(2*h) := by
  have hid := shiftedEdgeRoot_identity C he
  have hp := shiftedEdgeRoot_pos C he
  have hden : 0<2*a+shiftedEdgeRoot C a := by
    simpa [shiftedEdgeRoot] using Chart.stableRoot_pos C
  have hquad : 0≤(1-c^2)*(shiftedEdgeRoot C a)^2 :=
    mul_nonneg (by nlinarith [mul_pos (sub_pos.mpr hc.2) (show 0<1+c by linarith [hc.1])]) (sq_nonneg _)
  have herr : 0≤shiftedEdgeRoot C a*(1+D-c*shiftedEdgeRoot C a)^2/
      (2*a+shiftedEdgeRoot C a) := by positivity
  apply (le_div_iff₀ (by positivity : 0<2*h)).mpr
  linarith

def edgeRootLimit (c h : ℝ) : ℝ := 1/(Real.sqrt (h^2+1-c^2)+h)

theorem edgeRootLimit_pos {c h : ℝ} (hh : 0<h) : 0<edgeRootLimit c h := by
  unfold edgeRootLimit
  positivity

theorem edgeRootLimit_identity {c h : ℝ} (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) :
    (1-c^2)*(edgeRootLimit c h)^2+2*h*edgeRootLimit c h=1 := by
  have hs : 0<h^2+1-c^2 := by nlinarith [sq_nonneg h,mul_pos (sub_pos.mpr hc.2) (show 0<1+c by linarith [hc.1])]
  have hsqrt := Real.sq_sqrt hs.le
  have hd : Real.sqrt (h^2+1-c^2)+h≠0 := by positivity
  unfold edgeRootLimit
  field_simp [hd]
  nlinarith

end polyak.FareyPlateau
