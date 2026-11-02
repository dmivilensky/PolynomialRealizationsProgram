import krylov.Functions.ReferencePlaneRFCFNativeOutput
import krylov.Functions.PlanarRFCFScale

/-!
Article: main_krylov, thm:Fplanar, uniform original full-n RFC-F response.
Use: discharge every actual scalar search-domain and model inverse condition
before taking the full original tensor supremum. Source: genuine small-source
domain, actual native full-window dictionary and exact tensor homogeneity.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods krylov.Correction
  krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

set_option maxHeartbeats 1200000 in
/-- The literal original full-n RFC-F cycle on the genuine entire scalar
source family has exactly the sharp binary objective, uniformly over bounded
positive tensor shrinks. All native domains, actual queries and true model
solves are conclusions of the original scalar construction.
Article: main_krylov, thm:Fplanar, full native C_Y response. -/
theorem referencePlaneCubic_rfcFPoint_uniform_norm_remainder
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount A hA g=k+2) (U : ℝ) (hU : 0<U) :
    ∃ R ep C : ℝ, 0<R ∧ 0<ep ∧ 0<C ∧ ∀ ε α : ℝ, 0<ε → ε<ep → 0<α → α≤U →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      let f := referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α t)
      |‖(metricCoordinates A hA).symm
          (gradient f (rfcFPoint (metricCoordinates A hA) f (gradient f) R 0 (k+1)))‖-
        α^2*(referencePlaneRatio A hA g)^2/4*
          krylov.Tensor.BinaryCubic.rfcObjective (referencePlaneRatio A hA g) t*
          ‖canonicalCGStep A g 0‖^3*ε^3|≤C*ε^4 := by
  have hN : 2≤referenceAtomCount A hA g := by omega
  have hp := (referencePlane_sample_lines A hA g hN).1
  have hr := (referencePlane_sample_lines A hA g hN).2.1
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  obtain ⟨R,ed,hR,hed,hdom⟩ := referencePlane_small_source_domain A hA g hN U hU
  obtain ⟨M,hM,hbounds⟩ := planeRFCF_uniform_bounds r
  obtain ⟨el,Cl,hel,hCl,hresponse⟩ := planeRFCFOutput_scaled_norm_remainder r hr.ne'
  let ep := min ed (min (1/(2*(p*U*M+1))) (el/(U*p+1)))
  refine ⟨R,ep,Cl*U^3*p^4,hR,by dsimp only [ep]; positivity,by positivity,?_⟩
  intro ε α hε he hα hαU t ht
  dsimp only
  have hcount : referenceAtomCount A hA (ε • g)=k+2 := by rw [referenceAtomCount_scalar A hA g ε hε.ne',hc]
  have hd := hdom ε hε (he.trans_le (min_le_left _ _)) α hα.le hαU t ht
  have hMscaled : ‖planeRFCFModelOperator r (scaleBinaryCubic α t)‖≤U*M := by
    rw [planeRFCFModelOperator_scale,norm_smul,Real.norm_of_nonneg hα.le]
    exact mul_le_mul hαU (hbounds t ht).2.2 (norm_nonneg _) hU.le
  have hsmall : ‖canonicalCGStep A (ε • g) 0‖*
      ‖planeRFCFModelOperator (referencePlaneRatio A hA (ε • g)) (scaleBinaryCubic α t)‖≤1/2 := by
    rw [referencePlaneFirstLength_scalar A hA g hε,referencePlaneRatio_scalar A hA g hε]
    have hh := (lt_div_iff₀ (by positivity : 0<2*(p*U*M+1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    exact (mul_le_mul_of_nonneg_left hMscaled (by positivity : 0≤ε*p)).trans (by nlinarith only [hh,hε])
  have hnorm := referencePlaneCubic_rfcFPoint_gradient_norm A hA (ε • g) hcount
    (scaleBinaryCubic α t) R hd.1 hd.2 hsmall
  rw [referencePlaneFirstLength_scalar A hA g hε,referencePlaneRatio_scalar A hA g hε] at hnorm
  rw [hnorm]
  have hαp : α*(ε*p)<el := by
    have hh := (lt_div_iff₀ (by positivity : 0<U*p+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hh,mul_le_mul_of_nonneg_right hαU (by positivity : 0≤ε*p),hε]
  have hb := hresponse (ε*p) α (mul_pos hε hp) hα hαp t ht
  have hcoeff : α^2*(r^2/4*krylov.Tensor.BinaryCubic.rfcObjective r t)*(ε*p)^3=
      α^2*r^2/4*krylov.Tensor.BinaryCubic.rfcObjective r t*p^3*ε^3 := by ring
  rw [hcoeff] at hb
  apply hb.trans
  have hu3 := pow_le_pow_left₀ hα.le hαU 3
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu3 hCl.le) (pow_nonneg (by positivity : 0≤ε*p) 4)).trans_eq
    (by ring)

end
end krylov.Functions
