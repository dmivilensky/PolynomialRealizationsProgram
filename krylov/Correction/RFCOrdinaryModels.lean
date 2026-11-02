import krylov.Correction.RFCNonstagnatingModels

/-!
Article: main_krylov, thm:UCq, whole spectral-class ordinary RFC models.
Use: Transfer the genuinely derived uniform observed conditioning and gate
bounds to the original ordinary RFC executor with constants depending only
on dimension and spectral condition ratio.
Source: proved actual nonstagnating measured models at fixed shadow threshold
one half and exact equality of complete real accepted-prefix histories.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Ordinary RFC has a genuine uniform nonstagnating tube on the entire spectral class in which every active model has its derived inverse, both true accepted tests and the original linear step-normalized model bound.
Use: Supply the actual ordinary-RFC model and gate part of the original uniform theorem.
Article: main_krylov, thm:UCq.
Proof: Fix the auxiliary actual gate threshold at one half before choosing constants, so they depend only on dimension and condition ratio. The genuine nonstagnating-prefix theorem proves all real preterminal tests pass. Exact equality of the complete measured histories transfers every actual model, solve and decision to the original ordinary executor, including its unrestricted nonzero final direction.
-/
theorem ordinary_uniform_nonstagnating_models (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ ε₀ Cₘ : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<Cₘ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
      let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (∀ k≤n-1, methodRun (gatedMethod fullMemory (1/2)) A B g k=methodRun m A B g k) ∧
      (∀ k<n,
        let H := methodRun m A B g k
        let W := selectedWindow fullMemory H
        let d := m.direction H
        d≠0 →
        IsUnit (crossGram (windowImages W) (windowSteps W)).det ∧
        spectralGate (1/2) ((d,A k d)::W) ∧ ‖windowDefect W‖<1 ∧
        ‖rescaleModel (pairModel (Fin.cons (R d) (primalWindow base (windowSteps W)))
          (Fin.cons (canonicalOperator base (A k) (R d)) (dualWindow base (windowImages W))))
          (fun i => ‖(Fin.cons (R d) (primalWindow base (windowSteps W)) : Fin (W.length+1) → EuclideanSpace ℝ (Fin n)) i‖⁻¹)-1‖≤Cₘ*ε) := by
  obtain ⟨M,δ,C,hM,hδ,hC,hmodels⟩ := gated_uniform_nonstagnating_models n hn κ (1/2) hκ (by norm_num) (by norm_num)
  refine ⟨M,δ,C,hM,hδ,hC,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  let mg := gatedMethod fullMemory (1/2) (E := EuclideanSpace ℝ (Fin n))
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  have hbound := hmodels base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  have heq := gated_actual_passed_prefix_eq_rfc fullMemory (1/2) A B g (n-1) hbound.1
  dsimp only
  refine ⟨heq,?_⟩
  intro k hk hd
  have hh := heq k (by omega)
  have hd' : mg.direction (methodRun mg A B g k)≠0 := by
    rw [hh]
    exact hd
  have ht := hbound.2 k hk hd'
  rw [hh] at ht
  exact ht

end
end krylov.Correction
