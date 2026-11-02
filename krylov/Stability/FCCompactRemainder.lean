import krylov.Stability.AnalyticFC
import krylov.Stability.CompactCoefficients
import krylov.Stability.WeightedCompactTaylor

/-!
Article: main_krylov, lem:U(a,b,d), actual compact-reference FC Taylor bounds.
Use: apply the common compact Taylor calculus to the genuine adaptive FC
terminal gradient, deriving regularity from the actual quadratic reference domains.
Source: the proved executed FC analytic induction and the compact integral Taylor theorem.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped Topology InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The actual FC terminal gradient has compact-uniform Taylor bounds through every finite order near compact quadratic references.
Use: no regularity or Taylor remainder of the adaptive trajectory is assumed.
Article: main_krylov, lem:U(a,d), genuine compact FC cycle map.
Proof: actual reference CG domains imply actual FC analyticity at every
compact reference; its genuine open analytic locus supplies a common smooth
domain, to which the proved compact multidimensional Taylor theorem applies. -/
theorem quadraticFC_compact_taylor (A : X → ℕ → E →L[ℝ] E) (g : X → E) (N r : ℕ)
    (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ Q.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ ∀ i<N, CG.gradient Q (g x) i≠0) :
    let Φ := fun p => fcGradient fullMemory (A p) (g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k := by
  -- The open domain is the true analytic locus of the actual computed terminal gradient.
  let Φ := fun p => fcGradient fullMemory (A p) (g p) N
  have hΦ : ∀ x∈K, AnalyticAt ℝ Φ x := by
    intro x hx
    obtain ⟨Q,hAx,hQ,hpos,hpre⟩ := hquad x hx
    exact (quadraticFC_prefix_analytic A g x (hA x hx) (hg x hx) Q hAx hQ hpos N hpre).1
  apply compact_taylor_remainders Φ r {p | AnalyticAt ℝ Φ p} K (isOpen_analyticAt ℝ Φ) hK hΦ
  intro p hp
  exact hp.contDiffAt.contDiffWithinAt

/-- The genuine compact FC Taylor estimate admits the actual positive continuous reference-error factor.
Use: specialize e to the canonical initial-error norm once its reference parameterization is fixed.
Article: main_krylov, lem:U(a), weighted actual FC compact remainder.
Proof: the actual quadratic executions establish analyticity at the entire
compact reference; the proved weighted Taylor theorem supplies the uniform
neighborhood and absorbs the genuine positive error factor by its compact minimum. -/
theorem quadraticFC_compact_weighted_taylor (A : X → ℕ → E →L[ℝ] E) (g : X → E)
    (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ Q.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ ∀ i<N, CG.gradient Q (g x) i≠0)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun p => fcGradient fullMemory (A p) (g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k*e x := by
  -- The weight is an actual continuous reference quantity, never an assumed remainder constant.
  let Φ := fun p => fcGradient fullMemory (A p) (g p) N
  have hΦ : ∀ x∈K, AnalyticAt ℝ Φ x := by
    intro x hx
    obtain ⟨Q,hAx,hQ,hpos,hpre⟩ := hquad x hx
    exact (quadraticFC_prefix_analytic A g x (hA x hx) (hg x hx) Q hAx hQ hpos N hpre).1
  apply compact_weighted_taylor Φ e r {p | AnalyticAt ℝ Φ p} K (isOpen_analyticAt ℝ Φ) hK hΦ
    (fun _ hp => hp.contDiffAt.contDiffWithinAt) he hepos

end
end krylov.Stability
