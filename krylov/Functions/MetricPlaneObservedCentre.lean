import krylov.Functions.ScalarValueFinalRules
import krylov.Functions.HilbertPlaneValueModel
import krylov.Functions.PlanarObservedCentre

/-!
Article: main_krylov, thm:Fplanar, observed full-dimensional centre.
Use: transport the actual endpoint-only coefficient observer and the
attaining one-correction centre through a genuine Hilbert plane and the
fixed positive reference coordinates. Source: actual gradient chain rule,
quadratic defect cancellation and the established planar centre upper bound.
-/
namespace krylov.Functions
noncomputable section
open Finset krylov.Methods krylov.Reference krylov.Tensor.BinaryCubic
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The true physical gradient pairing is exactly the canonical pairing,
with the actual searched direction transported by the reference root.
Article: main_krylov, thm:Fplanar. -/
theorem metricHilbertPlaneGradient_pair (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (x v : E) :
    inner ℝ (gradient (metricHilbertPlaneObjective S e h m p r t) x) v=
      inner ℝ (gradient (hilbertPlaneObjective e h m p r t) (S x)) (S v) := by
  calc
    _=inner ℝ (S (S.symm (gradient (metricHilbertPlaneObjective S e h m p r t) x))) v := by
      rw [S.apply_symm_apply]
    _=inner ℝ (S.symm (gradient (metricHilbertPlaneObjective S e h m p r t) x)) (S v) :=
      hS.apply_clm _ _
    _=_ := by rw [metricHilbertPlaneGradient_normalized S hS]

/-- The observed physical trapezoid defect is exactly the genuine planar
defect, with the entire orthogonal quadratic cancelling.
Article: main_krylov, thm:Fplanar. -/
theorem metricHilbertPlane_value_defect (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E) (p r : ℝ)
    (t : krylov.Tensor.BinaryCubic) (a s : E) :
    segmentValueDefect (metricHilbertPlaneObjective S e h m p r t)
      (fun x=>innerSL ℝ (gradient (metricHilbertPlaneObjective S e h m p r t) x)) a s=
    segmentValueDefect (planeCubicObjective p r t)
      (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
      (hilbertPlaneProject e h (S a)) (hilbertPlaneProject e h (S s)) := by
  rw [←hilbertPlane_value_defect e h m p r t (S a) (S s)]
  simp only [segmentValueDefect,innerSL_apply_apply]
  rw [metricHilbertPlaneGradient_pair S hS,metricHilbertPlaneGradient_pair S hS]
  simp only [metricHilbertPlaneObjective,coordinateObjective,ContinuousLinearEquiv.symm_symm,map_add]

/-- The full-space actual normalized gradient at a lifted plane output
has exactly the planar gradient norm. Article: thm:Fplanar. -/
theorem metricHilbertPlaneGradient_lifted_norm (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (e h m : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (hm : hilbertPlaneProject e h m=0) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (z : Plane) :
    ‖S.symm (gradient (metricHilbertPlaneObjective S e h m p r t)
      (S.symm (hilbertPlaneEmbed e h z+m)))‖=‖gradient (planeCubicObjective p r t) z‖ := by
  rw [metricHilbertPlaneGradient_normalized S hS,S.apply_symm_apply,
    hilbertPlaneGradient_actual,hilbertPlaneGradient,map_add,
    hilbertPlaneProject_embed e h he hh heh,hm,add_zero]
  have hc : hilbertPlaneEmbed e h (gradient (planeCubicObjective p r t) z)+
      (hilbertPlaneEmbed e h z+m)-hilbertPlaneEmbed e h z-m=
      hilbertPlaneEmbed e h (gradient (planeCubicObjective p r t) z) := by abel
  rw [hc,hilbertPlaneEmbed_norm e h he hh heh]

/-- The three observed coefficients extracted only from actual first/last
defects and the actual normalized terminal gradient.
Article: main_krylov, thm:Fplanar. -/
def metricPlaneObservedBinaryData (S : E ≃L[ℝ] E) (e : E)
    (p r δ₀ δₗ : ℝ) (gₗ : E) : Observation :=
  ⟨-12*δ₀/p^3,2*inner ℝ e (S.symm gₗ)/(r*p^2),-12*δₗ/(r*p)^3⟩

/-- Genuine planar first and last defects recover their pure tensor
coefficients with the printed constants. Article: thm:Fplanar. -/
theorem plane_observed_pure_coefficients (p r : ℝ) (hp : p≠0) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) :
    let f := planeCubicObjective p r t
    let G := gradient f;
    -12*segmentValueDefect f (fun x=>innerSL ℝ (G x)) 0 (planeOfPair (p,0))/p^3=t.t0 ∧
    -12*segmentValueDefect f (fun x=>innerSL ℝ (G x)) (planeOfPair (p,0)) (planeOfPair (0,r*p))/(r*p)^3=t.t3 := by
  have ho := planeObservedBinaryData_eq p r hp hr t
  have h0 := congrArg Observation.t0 ho
  have h3 := congrArg Observation.t3 ho
  dsimp only [planeObservedBinaryData,observe] at h0 h3
  refine ⟨?_,?_⟩
  · simp only [segmentValueDefect,zero_add,innerSL_apply_apply]
    convert h0 using 1
    simp only [inner_add_left]
    ring
  · have hz : planeOfPair (p,0)+planeOfPair (0,r*p)=planeOfPair (p,r*p) := by
      rw [←planeOfPair_add]; congr 1; ext <;> simp
    simp only [segmentValueDefect,hz,innerSL_apply_apply]
    convert h3 using 1
    simp only [inner_add_left]
    ring

/-- A pair's defect calculated solely from its retained endpoint values,
gradients and actual line step. Article: main_krylov, thm:Fplanar. -/
def observedPairDefect {N : ℕ} (data : FunctionSearchTranscript E N) (i : Fin N) : ℝ :=
  data.values ⟨i.val+1,by omega⟩-data.values ⟨i.val,by omega⟩-
    inner ℝ (data.gradients ⟨i.val,by omega⟩+data.gradients ⟨i.val+1,by omega⟩) (data.lineSteps i)/2

/-- On a genuine CG path the retained endpoint computation is exactly the
actual scalar segment defect. Article: main_krylov, thm:Fplanar. -/
theorem observedPairDefect_reference (f : E → ℝ) (Q : E →L[ℝ] E) (g : E)
    (N : ℕ) (i : Fin N) :
    observedPairDefect (functionSearchTranscript f (CG.displacement Q g) (referenceStep Q g) N) i=
      segmentValueDefect f (fun x=>innerSL ℝ (gradient f x)) (CG.displacement Q g i.val) (referenceStep Q g i.val) := by
  simp only [observedPairDefect,functionSearchTranscript,segmentValueDefect,CG.displacement_succ,
    referenceStep,innerSL_apply_apply,inner_add_left]

/-- The full observed-data centre uses the actual metric lengths and plane
directions of its first and last retained steps. The tensor is absent.
Article: main_krylov, thm:Fplanar. -/
def metricPlaneCentreData {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (data : FunctionSearchTranscript E N) : Observation :=
  let s₀ := data.lineSteps ⟨0,hN⟩
  let sₗ := data.lineSteps ⟨N-1,by omega⟩
  let p := ‖S s₀‖
  let r := ‖S sₗ‖/p
  metricPlaneObservedBinaryData S (NormedSpace.normalize (S s₀)) p r
    (observedPairDefect data ⟨0,hN⟩) (observedPairDefect data ⟨N-1,by omega⟩)
    (observedFinalGradient data)

/-- Explicit data-only first/last-step coefficients of the attaining
centre correction. Article: main_krylov, thm:Fplanar. -/
def metricPlaneCentreCoefficients {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (_H : History E) (data : FunctionSearchTranscript E N) (i : Fin N) : ℝ :=
  let p := ‖S (data.lineSteps ⟨0,hN⟩)‖
  let v := ‖S (data.lineSteps ⟨N-1,by omega⟩)‖
  let z := planeCentreOutput (v/p) p (metricPlaneCentreData S hN data)
  (if i=⟨0,hN⟩ then (z 0-p)/p else 0)+
    (if i=⟨N-1,by omega⟩ then (z 1-v)/v else 0)

/-- A genuine original retained-span one-correction final policy.
All information is actual endpoint data, and global quadratic-zero
behaviour follows from ScalarValueFinalRules for these coefficients.
Article: main_krylov, thm:Fplanar. -/
def metricPlaneCentreFinalPolicy {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N) :
    History E → FunctionSearchTranscript E N → E :=
  observedSpanFinalPolicy hN (metricPlaneCentreCoefficients S hN)

omit [CompleteSpace E] in
/-- The centre displacement is literally a combination of the first and
last retained physical steps. Article: main_krylov, thm:Fplanar. -/
theorem metricPlaneCentre_sum {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (H : History E) (data : FunctionSearchTranscript E N) :
    ∑ i,metricPlaneCentreCoefficients S hN H data i • data.lineSteps i=
      let p := ‖S (data.lineSteps ⟨0,hN⟩)‖
      let v := ‖S (data.lineSteps ⟨N-1,by omega⟩)‖
      let z := planeCentreOutput (v/p) p (metricPlaneCentreData S hN data)
      ((z 0-p)/p) • data.lineSteps ⟨0,hN⟩+((z 1-v)/v) • data.lineSteps ⟨N-1,by omega⟩ := by
  classical
  simp only [metricPlaneCentreCoefficients,add_smul,sum_add_distrib,ite_smul,zero_smul]
  simp

end
end krylov.Functions
