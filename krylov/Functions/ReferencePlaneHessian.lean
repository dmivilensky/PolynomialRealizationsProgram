import krylov.Functions.MetricHilbertPlaneSharpSources
import krylov.Functions.ReferencePlaneScaling
import krylov.Nonlinear.AveragedComparison
import krylov.Nonlinear.CoordinateLipschitz

/-!
Article: main_krylov, prop:Fcycle(iii), actual observed and true metrics.
Use: retain the genuine derivative of the full scalar source and the genuine
first-segment Hessian average. Source: scalar coordinate differentiation,
Bochner-integral congruence and the sharp half-segment Lipschitz estimate.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set chebyshev1.Nonlinear krylov.Reference krylov.Secant krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual physical Hessian field of the full lifted scalar cubic.
Article: main_krylov, prop:Fcycle(iii). -/
def metricHilbertPlaneHessian (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) :=
  coordinateDerivative (metricCoordinates A hA).symm (hilbertPlaneHessian e h p r t)

/-- The displayed physical field differentiates the actual scalar gradient
at every point. Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneGradient_hasFDerivAt
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h m : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gradient (metricHilbertPlaneObjective (metricCoordinates A hA) e h m p r t))
      (metricHilbertPlaneHessian A hA e h p r t x) x := by
  let S := metricCoordinates A hA
  have hs : S.toContinuousLinearMap.IsSymmetric := metricPullback_symmetric A hA
  have heq : gradient (metricHilbertPlaneObjective S e h m p r t)=
      coordinateGradient S.symm (gradient (hilbertPlaneObjective e h m p r t)) := by
    funext y
    exact gradient_coordinateObjective S.symm hs _ y
      (hilbertPlaneObjective_hasFDerivAt e h m p r t (S y)).differentiableAt
  rw [heq]
  exact coordinateGradient_hasFDerivAt S.symm _ _ x
    (hilbertPlaneGradient_hasFDerivAt e h m p r t (S x))

/-- Positive-root congruence is exactly the physical matrix of the true
transported operator. Article: main_krylov, prop:Fcycle(iii). -/
theorem metricCongruence_physicalMatrix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm B)=
      metricRoot A*physicalOperatorMatrix B*metricRoot A := by
  apply (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).injective
  change cgOperator _=cgOperator _
  rw [physicalOperatorMatrix_operator]
  apply ContinuousLinearMap.ext
  intro v
  change cgOperator (metricRoot A) (B (cgOperator (metricRoot A) v))=_
  simp only [cgOperator,map_mul,mul_apply_eq_comp]
  change _=cgOperator (metricRoot A) (cgOperator (physicalOperatorMatrix B) (cgOperator (metricRoot A) v))
  rw [physicalOperatorMatrix_operator]
  rfl

/-- Physical true-Hessian drift is bounded by the fixed reference-root
constant times actual canonical drift. Article: prop:Fcycle(iii). -/
theorem metricCongruence_physicalMatrix_drift (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm B)-A‖≤
      ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*‖B-ContinuousLinearMap.id ℝ _‖ := by
  have hid : physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm
      (ContinuousLinearMap.id ℝ _))=A := by
    rw [metricCongruence_physicalMatrix]
    have hi : physicalOperatorMatrix (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))=1 := by
      change (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).symm 1=1
      exact map_one _
    rw [hi,mul_one,metricRoot_square A hA]
  calc
    _ = ‖physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm B)-
        physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm (ContinuousLinearMap.id ℝ _))‖ :=
      congrArg (fun M=>‖physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm B)-M‖) hid.symm
    _ = ‖coordinateCongruence (metricCoordinates A hA).symm (B-ContinuousLinearMap.id ℝ _)‖ := by
      rw [←physicalOperatorMatrix_sub,←map_sub,physicalOperatorMatrix_norm]
    _ ≤ _ := coordinateCongruence_norm_le (metricCoordinates A hA).symm _

/-- The actual physical observed matrix is the genuine average of the true
scalar Hessian along its first reference segment, rather than a supplied model.
Article: main_krylov, prop:Fcycle(iii), actual A₀. -/
def metricHilbertPlaneFirstSecant (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (σ : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  physicalOperatorMatrix (averagedDerivative (metricHilbertPlaneHessian A hA e h p r t)
    0 ((metricCoordinates A hA).symm σ))

set_option maxHeartbeats 800000 in
/-- The actual observed first secant satisfies a quantitative independent
metric drift bound, derived from the true scalar Hessian and actual segment.
Article: main_krylov, prop:Fcycle(iii). -/
theorem metricHilbertPlaneFirstSecant_drift
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (p r α : ℝ) (hα : 0≤α) {t : krylov.Tensor.BinaryCubic} (ht : t.InBall)
    (σ : EuclideanSpace ℝ (Fin n)) :
    ‖metricHilbertPlaneFirstSecant A hA e h p r (scaleBinaryCubic α t) σ-A‖≤
      ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*
        (α*‖σ‖/2+‖hilbertPlaneHessian e h p r (scaleBinaryCubic α t) 0-ContinuousLinearMap.id ℝ _‖) := by
  let H := hilbertPlaneHessian e h p r (scaleBinaryCubic α t)
  have hL := hilbertPlaneHessian_lipschitz e h he hh heh p r α hα ht
  have hc : ContinuousOn (fun s : ℝ=>H (0+s • σ)) (Icc 0 1) :=
    hL.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)) |>.continuousOn
  have heq : metricHilbertPlaneFirstSecant A hA e h p r (scaleBinaryCubic α t) σ=
      physicalOperatorMatrix (coordinateCongruence (metricCoordinates A hA).symm (averagedDerivative H 0 σ)) := by
    dsimp only [metricHilbertPlaneFirstSecant,metricHilbertPlaneHessian]
    rw [←map_zero (metricCoordinates A hA).symm,
      averagedDerivative_coordinate_operator (metricCoordinates A hA).symm H 0 σ hc]
    rw [map_zero]
  rw [heq]
  have havg := averagedDerivative_comparison_lipschitzOn H 0 σ 0 hL.lipschitzOnWith
    (fun _ _=>Set.mem_univ _) (fun _ _=>Set.mem_univ _)
  rw [averagedDerivative_zero,sub_zero,Real.coe_toNNReal _ hα] at havg
  have hb : ‖averagedDerivative H 0 σ-ContinuousLinearMap.id ℝ _‖≤
      α*‖σ‖/2+‖H 0-ContinuousLinearMap.id ℝ _‖ := by
    calc
      _ = ‖(averagedDerivative H 0 σ-H 0)+(H 0-ContinuousLinearMap.id ℝ _)‖ := by congr 1; abel
      _ ≤ ‖averagedDerivative H 0 σ-H 0‖+‖H 0-ContinuousLinearMap.id ℝ _‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [havg]
  exact (metricCongruence_physicalMatrix_drift A hA _).trans
    (mul_le_mul_of_nonneg_left hb (sq_nonneg _))

/-- The actual first-segment average of a bounded cubic source differs from
its prescribed positive reference by only first order in the actual source
scale. Article: main_krylov, prop:Fcycle(iii), actual A₀ normalization. -/
theorem metricHilbertPlaneFirstSecant_scaled_drift
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (σ : EuclideanSpace ℝ (Fin n)) (r U ε α : ℝ) (hε : 0≤ε) (hα : 0≤α) (hαU : α≤U)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) :
    ‖metricHilbertPlaneFirstSecant A hA e h (ε*‖σ‖) r (scaleBinaryCubic α t) (ε • σ)-A‖≤
      ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*
        (U*‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖))*ε := by
  have hp : 0≤ε*‖σ‖ := mul_nonneg hε (norm_nonneg _)
  have heq : planeOfPair (ε*‖σ‖,r*(ε*‖σ‖))=(ε*‖σ‖) • planeOfPair (1,r) := by
    rw [←planeOfPair_smul]
    congr 1
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring
  have h0 := (hilbertPlaneHessian_drift_norm e h he hh heh (ε*‖σ‖) r (scaleBinaryCubic α t) 0).trans
    (planeCubicHessian_scaled_norm_sub_id (ε*‖σ‖) r α hp hα ht (hilbertPlaneProject e h 0))
  rw [map_zero,zero_sub,norm_neg,heq,norm_smul,Real.norm_of_nonneg hp] at h0
  have hb := metricHilbertPlaneFirstSecant_drift A hA e h he hh heh (ε*‖σ‖) r α hα ht (ε • σ)
  rw [norm_smul,Real.norm_of_nonneg hε] at hb
  have htube : α*(ε*‖σ‖)/2+‖hilbertPlaneHessian e h (ε*‖σ‖) r (scaleBinaryCubic α t) 0-
      ContinuousLinearMap.id ℝ _‖≤U*‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)*ε := by
    calc
      _ ≤ α*(ε*‖σ‖)/2+(α*(ε*‖σ‖)*‖planeTerminalOperator r t‖+α*((ε*‖σ‖)*‖planeOfPair (1,r)‖)) :=
        by linarith only [h0]
      _ = α*(‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)*ε) := by ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hαU
          (by positivity : 0≤‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)*ε) using 1
        ring
  exact hb.trans ((mul_le_mul_of_nonneg_left htube (sq_nonneg _)).trans_eq (by ring))

/-- The canonical genuine first average has a uniform linear source drift.
Article: main_krylov, prop:Fcycle(iii), actual positive first-secant domain. -/
theorem hilbertPlaneFirstSecant_scaled_drift
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (σ : EuclideanSpace ℝ (Fin n)) (r U ε α : ℝ) (hε : 0≤ε) (hα : 0≤α) (hαU : α≤U)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) :
    ‖averagedDerivative (hilbertPlaneHessian e h (ε*‖σ‖) r (scaleBinaryCubic α t)) 0 (ε • σ)-
      ContinuousLinearMap.id ℝ _‖≤
        (U*‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖))*ε := by
  let H := hilbertPlaneHessian e h (ε*‖σ‖) r (scaleBinaryCubic α t)
  have hL := hilbertPlaneHessian_lipschitz e h he hh heh (ε*‖σ‖) r α hα ht
  have havg := averagedDerivative_comparison_lipschitzOn H 0 (ε • σ) 0 hL.lipschitzOnWith
    (fun _ _=>Set.mem_univ _) (fun _ _=>Set.mem_univ _)
  rw [averagedDerivative_zero,sub_zero,Real.coe_toNNReal _ hα,norm_smul,Real.norm_of_nonneg hε] at havg
  have hp : 0≤ε*‖σ‖ := mul_nonneg hε (norm_nonneg _)
  have heq : planeOfPair (ε*‖σ‖,r*(ε*‖σ‖))=(ε*‖σ‖) • planeOfPair (1,r) := by
    rw [←planeOfPair_smul]
    congr 1
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring
  have h0 := (hilbertPlaneHessian_drift_norm e h he hh heh (ε*‖σ‖) r (scaleBinaryCubic α t) 0).trans
    (planeCubicHessian_scaled_norm_sub_id (ε*‖σ‖) r α hp hα ht (hilbertPlaneProject e h 0))
  rw [map_zero,zero_sub,norm_neg,heq,norm_smul,Real.norm_of_nonneg hp] at h0
  calc
    _ ≤ ‖averagedDerivative H 0 (ε • σ)-H 0‖+‖H 0-ContinuousLinearMap.id ℝ _‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ α*(ε*‖σ‖)/2+(α*(ε*‖σ‖)*‖planeTerminalOperator r t‖+α*((ε*‖σ‖)*‖planeOfPair (1,r)‖)) := by
      linarith only [havg,h0]
    _ = α*(‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)*ε) := by ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right hαU
        (by positivity : 0≤‖σ‖*(1/2+‖planeTerminalOperator r t‖+‖planeOfPair (1,r)‖)*ε) using 1
      ring

/-- The actual physical first average is precisely the root congruence of
its actual canonical segment average. Article: prop:Fcycle(iii). -/
theorem metricHilbertPlaneFirstSecant_eq
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (σ : EuclideanSpace ℝ (Fin n)) :
    metricHilbertPlaneFirstSecant A hA e h p r t σ=
      metricRoot A*physicalOperatorMatrix (averagedDerivative (hilbertPlaneHessian e h p r t) 0 σ)*metricRoot A := by
  have hc : ContinuousOn (fun s : ℝ=>hilbertPlaneHessian e h p r t (0+s • σ)) (Icc 0 1) := by
    apply Continuous.continuousOn
    exact (continuous_iff_continuousAt.mpr (fun x=>(hilbertPlaneHessian_hasFDerivAt e h p r t x).continuousAt)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  dsimp only [metricHilbertPlaneFirstSecant,metricHilbertPlaneHessian]
  rw [←map_zero (metricCoordinates A hA).symm,
    averagedDerivative_coordinate_operator (metricCoordinates A hA).symm _ 0 σ hc,map_zero,
    metricCongruence_physicalMatrix]

/-- Small actual canonical segment drift proves that the genuine observed
physical first secant is positive definite. Article: prop:Fcycle(iii). -/
theorem metricHilbertPlaneFirstSecant_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (σ : EuclideanSpace ℝ (Fin n))
    (hd : ‖averagedDerivative (hilbertPlaneHessian e h p r t) 0 σ-ContinuousLinearMap.id ℝ _‖≤1/2) :
    (metricHilbertPlaneFirstSecant A hA e h p r t σ).PosDef := by
  let H := hilbertPlaneHessian e h p r t
  have hc : ContinuousOn (fun s : ℝ=>H (0+s • σ)) (Icc 0 1) := by
    exact (continuous_iff_continuousAt.mpr (fun x=>(hilbertPlaneHessian_hasFDerivAt e h p r t x).continuousAt)).comp
      (continuous_const.add (continuous_id.smul continuous_const)) |>.continuousOn
  have hs := averagedDerivative_symmetric H 0 σ hc (fun s _=>hilbertPlaneHessian_symmetric e h p r t (0+s • σ))
  have hp := physicalOperatorMatrix_posDef (averagedDerivative H 0 σ) hs (fun v hv=>
    (by positivity : 0<‖v‖^2/2).trans_le (inner_lower_of_identity_bound _ hd v))
  rw [metricHilbertPlaneFirstSecant_eq]
  exact metricPullbackMatrix_posDef A _ hA hp

end
end krylov.Functions
