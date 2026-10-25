import polyak.Boundary.P5.SlopeJoinAlgebra
import polyak.Boundary.P2.Analytic

/-! Source-linked zero envelope on both analytic continuations through Ga. -/
noncomputable section
namespace polyak.Boundary.P5.SlopeJoin
open Spectral Filter Envelope Polynomial
open scoped Topology

/-- Clearing the common positive denominator preserves the actual three active slacks. -/
theorem symbol_pairing {h : ℝ} (hh : 0≤h) (Z : Coordinates) {w : ℝ} (hw : 0<w ∧ w<1) :
    (1-h*Z 3)*symbol w (point (branchU h Z) (1+h) (branchX h Z))+
      h*Z 3*symbol w (point (branchU h Z) (1+h) (Z 2))=
      -(1+h)*(4*(1+h)^2-1)*(actualPrimal h Z 1 (-1)+
        w*actualPrimal h Z 2 1+(1-w)*actualPrimal h Z 3 1) := by
  have hg : 1≤1+h := by linarith
  have hd : (1+h)*(4*(1+h)^2-1)≠0 :=
    mul_ne_zero (by linarith) (by nlinarith [sq_nonneg h])
  have hpoint (c : ℝ) := dualSymbol_weights23_factor w hw.1.le hw.2.le hg (branchU h Z) c
  have hs (c : ℝ) : (1+h)*(4*(1+h)^2-1)*
      (normalizedLower (branchU h Z) (1+h) 1 c+
       w*normalizedUpper (branchU h Z) (1+h) 2 c+
       (1-w)*normalizedUpper (branchU h Z) (1+h) 3 c)=
      -symbol w (point (branchU h Z) (1+h) c) := by
    have hp:=hpoint c
    rw [dualSymbol_weights23] at hp
    have he:=(eq_div_iff hd).mp hp
    change _= -(-(1+h-c)*((1-c^2-(branchU h Z)^2)*cubicAlpha (1+h) w c-
      2*branchU h Z*(1-c^2)*quadraticBeta (1+h) w c))
    linear_combination he
  rw [actualPrimal_lower,actualPrimal_upper,actualPrimal_upper]
  dsimp only [branchU,branchX] at hs ⊢
  linear_combination (1-h*Z 3)*hs (-1/2+h*Z 1)+(h*Z 3)*hs (Z 2)

theorem symbol_pairing_zero {h : ℝ} (hh : 0≤h) {Z : Coordinates}
    (hz : regularSystem (h,Z)=0) {w : ℝ} (hw : 0<w ∧ w<1) :
    (1-h*Z 3)*symbol w (point (branchU h Z) (1+h) (branchX h Z))+
      h*Z 3*symbol w (point (branchU h Z) (1+h) (Z 2))=0 := by
  rw [symbol_pairing hh Z hw]
  obtain ⟨h1,h2,h3,_⟩:=active_slacks_zero hh hz
  rw [h1,h2,h3]
  ring

theorem p2Lift_primal {z : ℝ} (hz : z∈P2.parameterInterval) (h1 : P2.zeta1≤z)
    (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    actualPrimal (P2.G z-1) (p2Lift z) n σ=
      P2.reducedSlack z n σ/lagDenominator (P2.G z) n := by
  rw [actualPrimal_eq_raw_div (by linarith [P2.one_lt_G hz]) _ hn,
    p2Lift_rawBranch hz h1 n hn σ]
  rw [show 1+(P2.G z-1)=P2.G z by ring]

theorem p2_pairing_zero {z : ℝ} (hz : z∈P2.parameterInterval) (h1 : P2.zeta1≤z)
    {w : ℝ} (hw : 0<w ∧ w<1) :
    (1-P2.p z)*symbol w (point (P2.u z) (P2.G z) (P2.x z))+
      P2.p z*symbol w (point (P2.u z) (P2.G z) (P2.y z))=0 := by
  have he:=symbol_pairing (h:=P2.G z-1) (by linarith [P2.one_lt_G hz]) (p2Lift z) hw
  have hpr:=p2Lift_primal hz h1
  rw [hpr 1 (by omega) (-1),hpr 2 (by omega) 1,hpr 3 (by omega) 1,
    P2.lower1_zero hz,P2.upper2_zero hz,P2.upper3_zero hz] at he
  obtain ⟨hu,hx,hp,_⟩:=p2Lift_coordinates hz
  rw [hu,hx,hp,show 1+(P2.G z-1)=P2.G z by ring] at he
  rw [show p2Lift z 2=P2.y z from rfl] at he
  simpa only [zero_div,mul_zero,add_zero] using he

/-- Rational source codes give genuine differentiability at every interior source point. -/
theorem rational_differentiable {f : ℝ → ℝ} (code : P2.RationalCode P2.parameterInterval f)
    {z : ℝ} (hz : z∈Set.Ioo (3391/2000) (1699/1000)) : DifferentiableAt ℝ f z := by
  have hm : z∈P2.parameterInterval := ⟨hz.1.le,hz.2.le⟩
  have hn : DifferentiableAt ℝ (fun r : ℝ => aeval r code.numerator.toPoly) z :=
    code.numerator.toPoly.differentiableAt_aeval
  have he : DifferentiableAt ℝ (fun r : ℝ => aeval r code.denominator.toPoly) z :=
    code.denominator.toPoly.differentiableAt_aeval
  have hd:=hn.div he (code.denominator_ne z hm)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hz.1 hz.2] with r hr
  exact code.exact r ⟨hr.1.le,hr.2.le⟩

theorem p2_coordinates_differentiable {z : ℝ}
    (hz : z∈Set.Ioo (3391/2000) (1699/1000)) :
    DifferentiableAt ℝ P2.x z ∧ DifferentiableAt ℝ P2.y z ∧ DifferentiableAt ℝ P2.p z := by
  have hm : z∈P2.parameterInterval := ⟨hz.1.le,hz.2.le⟩
  have ha:=rational_differentiable P2.atomACode hz
  have hb:=rational_differentiable P2.atomBCode hz
  have hs:=((ha.pow 2).sub (hb.const_mul 4)).sqrt (P2.discriminant_pos hm).ne'
  have hx : DifferentiableAt ℝ P2.x z := by
    unfold P2.x
    exact (ha.neg.sub hs).div_const 2
  have hy : DifferentiableAt ℝ P2.y z := by
    unfold P2.y
    exact (ha.neg.add hs).div_const 2
  refine ⟨hx,hy,?_⟩
  unfold P2.p
  exact ((rational_differentiable P2.meanCosineCode hz).sub hx).div (hy.sub hx)
    (sub_pos.mpr (P2.roots_order hm).2.2).ne'

end polyak.Boundary.P5.SlopeJoin
