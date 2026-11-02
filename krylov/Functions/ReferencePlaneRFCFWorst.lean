import krylov.Functions.ReferencePlaneRFCFUniform
import krylov.Functions.PlanarRFCFWorst

/-!
Article: main_krylov, thm:Fplanar, the literal full-n RFC-F supremum.
Use: optimize the actual original scalar-function executor over the entire
binary tensor ball. Source: the proved uniform native response and an actual
maximizer of the original binary objective. No trajectory, inverse or output
expansion is included in the premises.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Reference krylov.Tensor krylov.Tensor.BinaryCubic krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- The real worst normalized gradient of the literal original full-n RFC-F
executor on all actual planar scalar sources. Article: thm:Fplanar. -/
def referencePlaneRFCFNativeWorst (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (R ε α : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ t : krylov.Tensor.BinaryCubic, t.InBall ∧
    let f := referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α t)
    v=‖(metricCoordinates A hA).symm
      (gradient f (rfcFPoint (metricCoordinates A hA) f (gradient f) R 0 (k+1)))‖}

set_option maxHeartbeats 1000000 in
/-- The literal original full-n RFC-F supremum has exactly the printed C_Y
coefficient, with a uniform fourth-order loss for every bounded positive
source shrink. Every actual query and final corrected model is executed.
Article: main_krylov, thm:Fplanar, genuine full-reference C_Y equality. -/
theorem referencePlaneRFCFNativeWorst_remainder
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount A hA g=k+2) (U : ℝ) (hU : 0<U) :
    ∃ R ep C : ℝ, 0<R ∧ 0<ep ∧ 0<C ∧ ∀ ε α : ℝ, 0<ε → ε<ep → 0<α → α≤U →
      |referencePlaneRFCFNativeWorst A hA g k R ε α-
        (α^2*referencePlaneRatio A hA g/4*modelMetricCoefficient (referencePlaneRatio A hA g)*
          ‖canonicalCGStep A g 0‖^3)*ε^3|≤C*ε^4 := by
  obtain ⟨R,ep,C,hR,hep,hC,hrem⟩ := referencePlaneCubic_rfcFPoint_uniform_norm_remainder A hA g hc U hU
  obtain ⟨tstar,htstar,hstar⟩ := exists_tensor_attaining_rfcWorst (referencePlaneRatio A hA g)
  refine ⟨R,ep,C,hR,hep,hC,?_⟩
  intro ε α hε he hα hαU
  let r := referencePlaneRatio A hA g
  let p := ‖canonicalCGStep A g 0‖
  let K := (α^2*r/4*modelMetricCoefficient r*p^3)*ε^3
  let F := fun t : krylov.Tensor.BinaryCubic=>
    let f := referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α t)
    ‖(metricCoordinates A hA).symm
      (gradient f (rfcFPoint (metricCoordinates A hA) f (gradient f) R 0 (k+1)))‖
  let V := {v : ℝ | ∃ t : krylov.Tensor.BinaryCubic, t.InBall ∧ v=F t}
  have hne : V.Nonempty := ⟨_,tstar,htstar,rfl⟩
  have hcoeff : α^2*r^2/4*rfcWorst r*p^3*ε^3=K := by
    dsimp only [K,modelMetricCoefficient]
    ring
  have hnorm t (ht : t.InBall) : |F t-α^2*r^2/4*rfcObjective r t*p^3*ε^3|≤C*ε^4 :=
    hrem ε α hε he hα hαU t ht
  have hupper v (hv : v∈V) : v≤K+C*ε^4 := by
    obtain ⟨t,ht,rfl⟩ := hv
    have hh := (abs_le.mp (hnorm t ht)).2
    have hb := le_csSup (rfcValues_bddAbove r) (show rfcObjective r t∈rfcValues r from ⟨t,ht,rfl⟩)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by positivity : 0≤α^2*r^2/4)) (by positivity : 0≤p^3))
      (pow_nonneg hε.le 3)
    change α^2*r^2/4*rfcObjective r t*p^3*ε^3≤α^2*r^2/4*rfcWorst r*p^3*ε^3 at hm
    rw [hcoeff] at hm
    linarith only [hh,hm]
  have hbounded : BddAbove V := ⟨K+C*ε^4,hupper⟩
  have hWupper : referencePlaneRFCFNativeWorst A hA g k R ε α≤K+C*ε^4 := csSup_le hne hupper
  have hWlower : K-C*ε^4≤referencePlaneRFCFNativeWorst A hA g k R ε α := by
    have hh := (abs_le.mp (hnorm tstar htstar)).1
    change rfcObjective r tstar=rfcWorst r at hstar
    rw [hstar,hcoeff] at hh
    have hm : F tstar≤referencePlaneRFCFNativeWorst A hA g k R ε α := le_csSup hbounded ⟨tstar,htstar,rfl⟩
    linarith only [hh,hm]
  change |referencePlaneRFCFNativeWorst A hA g k R ε α-K|≤C*ε^4
  exact abs_le.mpr ⟨by linarith only [hWlower],by linarith only [hWupper]⟩

end
end krylov.Functions
