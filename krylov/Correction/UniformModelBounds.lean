import krylov.Correction.RFCOrdinaryModels

/-!
Article: main_krylov, thm:UCq, original uniform observed RFC bounds.
Use: Expose actual normalized observed models and true quantitative prefix
consequences in a compact reusable form for the final uniform response.
Source: proved genuine nonstagnating finite-history induction, actual measured
model identities and real correction-contamination estimates.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original actual observed model normalized by the genuine reference-metric norms of its own physical query columns.
Use: Apply the original quantitative uniform RFC results to the same actual executor.
Article: main_krylov, thm:UCq.
-/
def canonicalObservedModel (base : Matrix (Fin n) (Fin n) ℝ)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  rescaleModel (windowModel W) (fun i => ‖primalWindow base (windowSteps W) i‖⁻¹)

/-- The original physical normalized augmented model is exactly the true canonical finite-array model.
Use: Apply the original quantitative uniform RFC results to the same actual executor.
Article: main_krylov, thm:UCq.
Proof: Exact primal/dual model invariance and the real head/old-column metric dictionary identify both the actual matrix and its own genuine length normalizers.
-/
theorem canonicalObservedModel_augmented (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (d : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let U : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (R d) (primalWindow base (windowSteps W))
    let Z : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) :=
      Fin.cons (canonicalOperator base A (R d)) (dualWindow base (windowImages W))
    canonicalObservedModel base ((d,A d)::W)=rescaleModel (pairModel U Z) (fun i => ‖U i‖⁻¹) := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let U : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (R d) (primalWindow base (windowSteps W))
  let Z : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) :=
    Fin.cons (canonicalOperator base A (R d)) (dualWindow base (windowImages W))
  have hU : primalWindow base (windowSteps ((d,A d)::W))=U := by
    rw [windowSteps_cons]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hZ : dualWindow base (windowImages ((d,A d)::W))=Z := by
    rw [windowImages_cons]
    funext i
    exact Fin.cases (canonicalOperator_primal base hb A d).symm (fun _ => rfl) i
  dsimp only
  unfold canonicalObservedModel
  rw [← pairModel_window,← canonical_pairModel base hb,hU,hZ]
  rfl

/-- The actual active-iteration observed inverse, measured spectral and defect gates, and original step-normalized model allowance of a genuine probed run.
Use: Apply the original quantitative uniform RFC results to the same actual executor.
Article: main_krylov, thm:UCq.
-/
def activeObservedModelBounds (base : Matrix (Fin n) (Fin n) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (γ C ε : ℝ) : Prop :=
  ∀ k<N, let H := methodRun m A B g k
    let W := selectedWindow fullMemory H
    let d := m.direction H
    d≠0 → IsUnit (crossGram (windowImages W) (windowSteps W)).det ∧
      spectralGate γ ((d,A k d)::W) ∧ ‖windowDefect W‖<1 ∧
      ‖canonicalObservedModel base ((d,A k d)::W)-1‖≤C*ε

/-- One true uniform nonstagnation tube controls every active ordinary-RFC model directly in its original observed physical coordinates.
Use: Apply the original quantitative uniform RFC results to the same actual executor.
Article: main_krylov, thm:UCq.
Proof: Apply the proved complete actual ordinary model theorem and the exact physical/canonical normalized augmented-model identity.
-/
theorem ordinary_uniform_active_models (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ε₀ C : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      activeObservedModelBounds base (rfcMethod fullMemory 1) A B g n (1/2) C ε := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_nonstagnating_models n hn κ hκ
  refine ⟨M,δ,C,hM,hδ,hC,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  dsimp only [activeObservedModelBounds]
  intro k hk hd
  have ht := (hbound base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB).2 k hk hd
  refine ⟨ht.1,ht.2.1,ht.2.2.1,?_⟩
  rw [canonicalObservedModel_augmented base hb]
  exact ht.2.2.2

/-- The actual two-dimensional ordinary-RFC model and gate bounds hold uniformly without a nonstagnation condition for normalized full active references.
Use: Apply the original quantitative uniform RFC results to the same actual executor.
Article: main_krylov, thm:UCq.
Proof: In dimension two the reference nonstagnation error is exactly its initial unit error. Intersect the proved common radius with the reciprocal nonstagnation constant, making (N) automatic.
-/
theorem ordinary_two_dimensional_active_models (κ : ℝ) (hκ : 1≤κ) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
        (g : EuclideanSpace ℝ (Fin 2)) (ε : ℝ), 0<ε → ε≤ε₀ →
      ‖cgCanonicalError base g 0‖=1 → (∀ i<2, CG.gradient (cgOperator base) g i≠0) →
      (∀ i<2, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖≤ε) →
      (∀ i<2, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖≤ε) →
      activeObservedModelBounds base (rfcMethod fullMemory 1) A B g 2 (1/2) C ε := by
  obtain ⟨M,δ,C,hM,hδ,hC,hbound⟩ := ordinary_uniform_active_models 2 (by omega) κ hκ
  refine ⟨min δ (1/M),C,lt_min hδ (by positivity),hC,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hA hB
  have heδ := he.trans (min_le_left _ _)
  have heM : ε*M≤1 := (le_div_iff₀ hM).mp (he.trans (min_le_right _ _))
  apply hbound base hb μ hμ hspec A B g ε hε heδ hinit.le hpre ?_ hA hB
  simpa only [show (2 : ℕ)-2=0 by omega,hinit,mul_comm] using heM

end
end krylov.Correction
