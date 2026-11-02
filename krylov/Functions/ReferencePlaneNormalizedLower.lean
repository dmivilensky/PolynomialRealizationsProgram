import krylov.Functions.ReferencePlaneMethodLower
import krylov.Functions.ReferencePlaneOwnNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), complete original own-reference sharpness.
Use: combine actual causal scalar execution with genuine own-reference true-minimizer
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

set_option maxHeartbeats 1200000 in
/-- Original methods attain their unavoidable cubic true-error lower bound
in their OWN actually observed first-secant reference and true initial error.
All source construction, canonical tensor budgets, true minima, domain and
normalization estimates precede the actual method and its final policy.
Article: main_krylov, prop:Fcycle(iii), complete own-reference sharpness. -/
theorem referencePlane_all_methods_own_sharp_lower
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (a : ℝ) (ha : 0<a) (ha₁ : a<1) :
    ∃ t u : krylov.Tensor.BinaryCubic,
      Chord (referencePlaneRatio A hA g) t u ∧
      chordValue (referencePlaneRatio A hA g) t u=fibreMinimax (referencePlaneRatio A hA g) ∧
    ∃ R ep Cs Cκ C c : ℝ, 0<R ∧ 0<ep ∧ 0<Cs ∧ 0<Cκ ∧ 0<C ∧ 0<c ∧
      ∀ ε : ℝ, 0<ε → ε<ep →
      let α := 2*a*(1-Cs*(ε*‖canonicalCGStep A g 0‖))^3
      let τ := scaleBinaryCubic α t
      let υ := scaleBinaryCubic α u
      0<α ∧ α≤2*a ∧ ∃ z w : EuclideanSpace ℝ (Fin n),
        ReferencePlaneTrueMetricRealization A hA g ε a τ z ∧
        ReferencePlaneTrueMetricRealization A hA g ε a υ w ∧
        (referencePlaneObservedMatrix A hA g ε τ).PosDef ∧
        (referencePlaneObservedMatrix A hA g ε υ).PosDef ∧
        let et := referencePlaneTrueInitialError A hA g ε τ z
        let eu := referencePlaneTrueInitialError A hA g ε υ w
        c*ε≤et ∧ c*ε≤eu ∧
        |referencePlaneOwnCoefficient A hA g ε τ z/
          referenceTwoMetricFibreCoefficient A A g (referencePlaneInitialError A hA g)
            (referenceAtomCount A hA g-1)-1|≤Cκ*et ∧
        |referencePlaneOwnCoefficient A hA g ε υ w/
          referenceTwoMetricFibreCoefficient A A g (referencePlaneInitialError A hA g)
            (referenceAtomCount A hA g-1)-1|≤Cκ*eu ∧
        ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin n)), CGConsistent m →
        ∀ policy : History (EuclideanSpace ℝ (Fin n)) →
          FunctionSearchTranscript (EuclideanSpace ℝ (Fin n)) (referenceAtomCount A hA (ε • g)) →
            EuclideanSpace ℝ (Fin n),
        (1-C*et)*a^2*referencePlaneOwnCoefficient A hA g ε τ z*et^3≤
          referencePlaneActualError A hA g ε τ z (referencePlaneValueOutput A hA g ε τ R m policy) ∨
        (1-C*eu)*a^2*referencePlaneOwnCoefficient A hA g ε υ w*eu^3≤
          referencePlaneActualError A hA g ε υ w (referencePlaneValueOutput A hA g ε υ R m policy) := by
  obtain ⟨t,u,hch,hatt,es,Cs,M,E,hes,hCs,hM,hE,hsource⟩ := referencePlane_sharp_actual_sources A hA g hN a ha ha₁
  obtain ⟨R,ec,hR,hec,hcausal⟩ := referencePlane_small_source_final_output_equal A hA g hN (2*a) (by positivity)
  obtain ⟨en,Cκ,C,c,hen,hCκ,hC,hc,hnorm⟩ := referencePlane_own_normalization A hA g hN a (2*a) Cs M E
    ha (by positivity) hCs hM hE.le
  refine ⟨t,u,hch,hatt,R,min es (min ec en),Cs,Cκ,C,c,hR,by positivity,hCs,hCκ,hC,hc,?_⟩
  intro ε hε heps
  obtain ⟨hα,hαU,_,_,_,z,w,hz,hw,hzt,hwu,hHz,hHw,_,_,hlower⟩ :=
    hsource ε hε (heps.trans_le (min_le_left _ _))
  let α := 2*a*(1-Cs*(ε*‖canonicalCGStep A g 0‖))^3
  let τ := scaleBinaryCubic α t
  let υ := scaleBinaryCubic α u
  let zf := hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) z+
    ε • referencePlaneComplement A hA g
  let wf := hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) w+
    ε • referencePlaneComplement A hA g
  have hen' := heps.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hBt,het,hκt,hLt⟩ := hnorm ε hε hen' α hα.le hαU t hch.1 z hz hzt hHz
  obtain ⟨hBu,heu,hκu,hLu⟩ := hnorm ε hε hen' α hα.le hαU u hch.2.1 w hw hwu hHw
  refine ⟨hα,hαU,zf,wf,hzt,hwu,hBt,hBu,het,heu,hκt,hκu,?_⟩
  intro m hm policy
  have heq := hcausal ε hε (heps.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    α hα.le hαU t u hch.1 hch.2.1 (chord_observations hch) m hm policy
  change referencePlaneValueOutput A hA g ε υ R m policy=referencePlaneValueOutput A hA g ε τ R m policy at heq
  have hb : a^2*referenceFibreCoefficient A g (referenceAtomCount A hA g-1)*ε^3-E*ε^4≤
      max (referencePlaneActualError A hA g ε τ zf (referencePlaneValueOutput A hA g ε τ R m policy))
        (referencePlaneActualError A hA g ε υ wf (referencePlaneValueOutput A hA g ε υ R m policy)) := by
    rw [heq]
    convert! hlower (referencePlaneValueOutput A hA g ε τ R m policy) using 1
  exact (le_max_iff.mp hb).imp (hLt.trans ·) (hLu.trans ·)

end
end krylov.Functions
