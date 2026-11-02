import krylov.Stability.AnalyticRFC
import krylov.Stability.CompactAnalytic

/-!
Article: main_krylov, lem:U(a,d), genuine compact-reference RFC remainders.
Use: discharge actual repeated RFC regularity, strict gates and model domains
before applying the common compact Taylor theorem to its real terminal output.
Source: the proved adaptive RFC analytic execution and compact analytic-locus calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

omit [CompleteSpace E] [ProperSpace X] in
/-- The real adaptive repeated RFC terminal gradient has genuine joint analyticity on every actual compatible quadratic reference set.
Use: share the discharged reference regularity between compact Taylor and weighted compact Taylor applications.
Article: main_krylov, lem:U(d), actual RFC_k reference regularity.
Proof: each actual quadratic reference supplies the true static operators,
nonstagnant CG prefix and compatible retention rule to the proved actual gated
RFC analytic induction, including every real correction query. -/
theorem quadraticRFC_analyticOn_references (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (N : ℕ) (K : Set X)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => B p i) x) (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧
      (∀ k, CG.gradient Q (g x) k≠0 → 0<k → 0<memory k) ∧ ∀ i<N, CG.gradient Q (g x) i≠0) :
    ∀ x∈K, AnalyticAt ℝ (fun p => probedGradient (rfcMethod memory count) (A p) (B p) (g p) N) x := by
  intro x hx
  obtain ⟨Q,hAx,hBx,hQ,hpos,hm,hpre⟩ := hquad x hx
  exact (quadraticRFC_prefix_analytic memory count A B g x (hA x hx) (hB x hx) (hg x hx)
    Q hAx hBx hQ hpos hm N hpre).1

/-- Actual repeated RFC terminal gradients have compact-uniform Taylor remainders through every finite order.
Use: one actual neighborhood and constant cover the whole reference compact, after real gates and solves have been discharged.
Article: main_krylov, lem:U(a,d), compact actual RFC_k cycle remainder.
Proof: derive actual reference analyticity from the genuine executed RFC
induction, then apply the common compact analytic Taylor theorem. -/
theorem quadraticRFC_compact_taylor (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => B p i) x) (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧
      (∀ k, CG.gradient Q (g x) k≠0 → 0<k → 0<memory k) ∧ ∀ i<N, CG.gradient Q (g x) i≠0) :
    let Φ := fun p => probedGradient (rfcMethod memory count) (A p) (B p) (g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ k : ℕ, 1≤k → k≤r →
      ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k := by
  exact compact_analytic_taylor _ K hK
    (quadraticRFC_analyticOn_references memory count A B g N K hA hB hg hquad) r

/-- Actual repeated RFC compact Taylor remainders admit the genuine positive continuous reference-error factor.
Use: the source's initial-error normalization is absorbed uniformly on the actual compact set.
Article: main_krylov, lem:U(a,d), weighted compact actual RFC remainder.
Proof: the actual RFC reference induction supplies true analyticity;
the common weighted compact theorem supplies its true uniform remainder and reference normalization. -/
theorem quadraticRFC_compact_weighted_taylor (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => B p i) x) (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧
      (∀ k, CG.gradient Q (g x) k≠0 → 0<k → 0<memory k) ∧ ∀ i<N, CG.gradient Q (g x) i≠0)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun p => probedGradient (rfcMethod memory count) (A p) (B p) (g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ k : ℕ, 1≤k → k≤r →
      ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k*e x := by
  exact compact_analytic_weighted_taylor _ e K hK
    (quadraticRFC_analyticOn_references memory count A B g N K hA hB hg hquad) he hepos r

end
end krylov.Stability
