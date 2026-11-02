import jacobi.Variational.GreenMonotone
import jacobi.Variational.FredholmParameterTrace

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The genuine Green-ratio source is integrable on the product line: its exact
x-integral is 2*m(y)*g(y), integrable by the spectral margin. Fubini therefore
turns the spatial derivative integral into the same actual Green trace as
the spectral Fredholm derivative. No conditional Fubini or convergence
certificate is introduced for the infinite spatial domain.
Source: the proved Green-ratio integral and Bochner Fubini in mathlib.
Use: its integrable product bound licenses Fubini and uniform domination in the determinant identity.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual nonnegative product source for the derivative of the spatial reciprocal-diagonal functional.
Use: its integrable product bound licenses Fubini and uniform domination in the determinant identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenRatioSource (m : L1Source) (s : ℝ) (hs : 0≤s) (hp : s*observe m .top<1)
    (z : ℝ × ℝ) : ℝ := m.value z.2*(m.fredholmGreen s hs hp z.1 z.2/m.greenDiagonal s hs hp z.1)^2

/-- The actual Green ratio source is integrable on the full product line.
Use: licenses the spatial determinant derivative's Fubini interchange and its integrable majorant.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the exact actual Green-ratio integral gives each vertical norm
integral as 2*m(y)*g(y). The actual diagonal margin bounds 2g uniformly,
so this is integrable against the original L1 density. Apply genuine product integrability. -/
theorem L1Source.greenRatioSource_integrable (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) : Integrable (m.greenRatioSource s hs hp) (volume.prod volume) := by
  -- Joint measurability is obtained from the actual continuous Green kernel and its positive diagonal.
  let G := m.fredholmGreen s hs hp
  let g := m.greenDiagonal s hs hp
  let H := m.greenRatioSource s hs hp
  have hg : Continuous g := (m.greenDiagonal_contDiff hc hs hp).continuous
  have hH : Continuous H := (hc.comp continuous_snd).mul
    (((m.fredholmGreen_continuous hs hp).div (hg.comp continuous_fst)
      (fun z => (m.fredholmGreen_pos hs hp z.1 z.1).ne')).pow 2)
  have hi (y : ℝ) : Integrable (fun x => H (x,y)) :=
    (m.green_ratio_square_integral hc hs hp y).1.const_mul (m.value y)
  have hv (y : ℝ) : (∫ x,‖H (x,y)‖)=m.value y*(2*g y) := by
    change (∫ x,|m.value y*(G x y/g x)^2|)=m.value y*(2*g y)
    simp_rw [abs_of_nonneg (mul_nonneg (m.nonneg y) (sq_nonneg _))]
    rw [integral_const_mul,(m.green_ratio_square_integral hc hs hp y).2]
  have hB (y : ℝ) : ‖2*g y‖≤(1-s*observe m .top)⁻¹ := by
    have hdiag := m.fredholmGreen_diagonal hs hp y
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp only [g,L1Source.greenDiagonal]; linarith [hdiag.1])]
    calc
      _ ≤ 2*(1/(2*(1-s*observe m .top))) := mul_le_mul_of_nonneg_left hdiag.2 (by norm_num)
      _ = _ := by field_simp
  have hpair : Integrable (fun y => m.value y*(2*g y)) := by
    have hh := m.integrable.bdd_mul (hg.const_mul 2).aestronglyMeasurable (Eventually.of_forall hB)
    convert hh using 1
    funext y
    ring
  apply (integrable_prod_iff' hH.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hi,?_⟩
  have he : (fun y => ∫ x,‖H (x,y)‖)=fun y => m.value y*(2*g y) := funext hv
  rw [he]
  exact hpair

/-- The actual Green-ratio source has exactly the spatial trace integral supplied by the unit Wronskian.
Use: evaluates the integrated derivative of the reciprocal-diagonal determinant functional.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: actual product integrability licenses Fubini; each inner x-integral
is the proved exact Green-ratio square integral with the constant density factor removed. -/
theorem L1Source.greenRatioSource_integral (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    (∫ x,∫ y,m.greenRatioSource s hs hp (x,y))=
      ∫ y,m.value y*(2*m.greenDiagonal s hs hp y) := by
  have hi : Integrable (Function.uncurry (fun x y => m.greenRatioSource s hs hp (x,y)))
      (volume.prod volume) := m.greenRatioSource_integrable hc hs hp
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (∫ x,m.value y*(m.fredholmGreen s hs hp x y/m.greenDiagonal s hs hp x)^2)=_
    rw [integral_const_mul,(m.green_ratio_square_integral hc hs hp y).2]

/-- The genuine spatial derivative of the regularized Green integral has the exact spectral Green trace.
Use: equality of this trace with the actual Fredholm series derivative proves the final determinant identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the actual source is product-integrable. Subtract the original
integrable density, apply the proved Fubini value, and collect the literal
m*(2g-1) integrand. -/
theorem L1Source.greenSpatialSlope_trace (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    Integrable (fun x => (∫ y,m.greenRatioSource s hs hp (x,y))-m.value x) ∧
      (∫ x,(∫ y,m.greenRatioSource s hs hp (x,y))-m.value x)=
        ∫ x,m.value x*(2*m.fredholmGreen s hs hp x x-1) := by
  -- Fubini integrability is established before the signed mass regularization is subtracted.
  have hi := (m.greenRatioSource_integrable hc hs hp).integral_prod_left
  have hj := (m.greenRatioSource_integrable hc hs hp).integral_prod_right
  have hpair : Integrable (fun y => m.value y*(2*m.greenDiagonal s hs hp y)) := by
    apply hj.congr
    exact Eventually.of_forall fun y => by
      change (∫ x,m.value y*(m.fredholmGreen s hs hp x y/m.greenDiagonal s hs hp x)^2)=_
      rw [integral_const_mul,(m.green_ratio_square_integral hc hs hp y).2]
  refine ⟨hi.sub m.integrable,?_⟩
  rw [integral_sub hi m.integrable,m.greenRatioSource_integral hc hs hp,← integral_sub hpair m.integrable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change m.value x*(2*m.fredholmGreen s hs hp x x)-m.value x=m.value x*(2*m.fredholmGreen s hs hp x x-1)
    ring

end
end jacobi.Variational
