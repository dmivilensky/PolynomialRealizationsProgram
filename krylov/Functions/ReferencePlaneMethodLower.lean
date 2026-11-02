import krylov.Functions.ReferencePlaneSharpSources
import krylov.Functions.ReferencePlaneValueFibre

/-!
Article: main_krylov, prop:Fcycle(iii), original actual-method sharpness.
Use: combine actual causal scalar execution with genuine true-minimizer
self-concordant sources. One of two exactly indistinguishable scalar cubics
forces the printed cubic error on every original CG-consistent method with
an arbitrary data-only final correction. All constants precede the method.
Source: actual full-reference source realization and proved scalar replay.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The literal actual scalar output on the original scaled cubic family.
Article: main_krylov, prop:Fcycle(iii), genuine method class dictionary. -/
def referencePlaneValueOutput (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : krylov.Tensor.BinaryCubic) (R : ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (policy : History (EuclideanSpace ℝ (Fin n)) →
      FunctionSearchTranscript (EuclideanSpace ℝ (Fin n)) (referenceAtomCount A hA (ε • g)) →
        EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  scalarValueFinalOutput m (metricCoordinates A hA) (referencePlaneCubicObjective A hA (ε • g) t)
    R 0 (referenceAtomCount A hA (ε • g)) policy

/-- Error uses the true positive Hessian at the source's genuine minimum.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneActualError (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  metricHilbertPlaneMetricError A hA (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) t z x

set_option maxHeartbeats 1000000 in
/-- Every genuine original method has the sharp cubic true-error lower
coefficient on one of two actual indistinguishable self-concordant cubics.
The search radius, source pair and constants are uniform BEFORE the method
and every unrestricted causal final correction are chosen.
Article: main_krylov, prop:Fcycle(iii).
This includes the original one-correction class, since the final policy is
allowed every actually observed value, gradient and full searched line. -/
theorem referencePlane_all_methods_sharp_lower
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (a : ℝ) (ha : 0<a) (ha₁ : a<1) :
    ∃ t u : krylov.Tensor.BinaryCubic,
      Chord (referencePlaneRatio A hA g) t u ∧
      chordValue (referencePlaneRatio A hA g) t u=fibreMinimax (referencePlaneRatio A hA g) ∧
    ∃ R ep C E : ℝ, 0<R ∧ 0<ep ∧ 0<C ∧ 0<E ∧
      ∀ ε : ℝ, 0<ε → ε<ep →
      let α := 2*a*(1-C*(ε*‖canonicalCGStep A g 0‖))^3
      let τ := scaleBinaryCubic α t
      let υ := scaleBinaryCubic α u
      0<α ∧ α≤2*a ∧ ∃ z w : EuclideanSpace ℝ (Fin n),
        ReferencePlaneTrueMetricRealization A hA g ε a τ z ∧
        ReferencePlaneTrueMetricRealization A hA g ε a υ w ∧
        ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin n)), CGConsistent m →
        ∀ policy : History (EuclideanSpace ℝ (Fin n)) →
          FunctionSearchTranscript (EuclideanSpace ℝ (Fin n)) (referenceAtomCount A hA (ε • g)) →
            EuclideanSpace ℝ (Fin n),
        let L := a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)*ε^3-E*ε^4
        L≤referencePlaneActualError A hA g ε τ z (referencePlaneValueOutput A hA g ε τ R m policy) ∨
          L≤referencePlaneActualError A hA g ε υ w (referencePlaneValueOutput A hA g ε υ R m policy) := by
  obtain ⟨t,u,hch,hatt,es,C,_,E,hes,hC,_,hE,hsource⟩ := referencePlane_sharp_actual_sources A hA g hN a ha ha₁
  obtain ⟨R,ec,hR,hec,hcausal⟩ := referencePlane_small_source_final_output_equal A hA g hN (2*a) (by positivity)
  refine ⟨t,u,hch,hatt,R,min es ec,C,E,hR,lt_min hes hec,hC,hE,?_⟩
  intro ε hε heps
  obtain ⟨hα,hαU,_,_,_,z,w,_,_,hzt,hwu,_,_,_,_,hlower⟩ :=
    hsource ε hε (heps.trans_le (min_le_left _ _))
  let α := 2*a*(1-C*(ε*‖canonicalCGStep A g 0‖))^3
  let τ := scaleBinaryCubic α t
  let υ := scaleBinaryCubic α u
  let zf := hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) z+
    ε • referencePlaneComplement A hA g
  let wf := hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) w+
    ε • referencePlaneComplement A hA g
  refine ⟨hα,hαU,zf,wf,hzt,hwu,?_⟩
  intro m hm policy
  have heq := hcausal ε hε (heps.trans_le (min_le_right _ _)) α hα.le hαU t u
    hch.1 hch.2.1 (chord_observations hch) m hm policy
  change referencePlaneValueOutput A hA g ε υ R m policy=referencePlaneValueOutput A hA g ε τ R m policy at heq
  have hb : a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)*ε^3-E*ε^4≤
      max (referencePlaneActualError A hA g ε τ zf (referencePlaneValueOutput A hA g ε τ R m policy))
        (referencePlaneActualError A hA g ε υ wf (referencePlaneValueOutput A hA g ε υ R m policy)) := by
    rw [heq]
    convert! hlower (referencePlaneValueOutput A hA g ε τ R m policy) using 1
  exact le_max_iff.mp hb

end
end krylov.Functions
