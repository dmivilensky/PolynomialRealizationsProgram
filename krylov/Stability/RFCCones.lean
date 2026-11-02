import krylov.Stability.RFCCompactRemainder
import krylov.Stability.HomogeneousTaylor
import krylov.Methods.HomogeneousRFC

/-!
Article: main_krylov, lem:U(c,d), genuine RFC compact cones.
Use: apply the actual executed RFC scaling theorem to extend compact weighted
Taylor remainders to every positive scale with exactly the same constants.
Source: the proved actual RFC homogeneity, actual quadratic analytic domains,
and finite Taylor polynomial covariance under constant scalar multiplication.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Actual repeated RFC has the same compact Taylor constants on the entire positive initial-gradient cone.
Use: all regularity and homogeneity premises are proved for the true RFC policy, rather than supplied as an abstract expansion.
Article: main_krylov, lem:U(c,d), actual RFC cone estimate.
Proof: actual quadratic CG domains give actual analytic regularity at every
reference. The compact RFC theorem supplies one radius and constant. The actual
RFC trajectory scales exactly, so its genuine finite Taylor polynomial and
remainder scale by the same positive factor, leaving both constants unchanged. -/
theorem quadraticRFC_compact_cone_taylor (memory : ℕ → ℕ) (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hB : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => B p i) x)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧ Q.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧
      (∀ k, CG.gradient Q (g x) k≠0 → 0<k → 0<memory k) ∧ ∀ i<N, CG.gradient Q (g x) i≠0)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ∀ c : ℝ, 0<c →
      let Φc := fun p => probedGradient (rfcMethod memory count) (A p) (B p) (c • g p) N
      ‖Φc (x+h)-taylorPolynomial Φc k x h‖≤C*‖h‖^k*(c*e x) := by
  -- Use one genuine compact estimate before introducing any positive initial-gradient scale.
  obtain ⟨δ,C,hδ,hC,hrem⟩ := quadraticRFC_compact_weighted_taylor memory count A B g e N r K hK hA hB hg hquad he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh k hk hkr c hc
  let Φ := fun p => probedGradient (rfcMethod memory count) (A p) (B p) (g p) N
  have hΦ : ContDiffAt ℝ k Φ x := by
    exact (quadraticRFC_analyticOn_references memory count A B g N K hA hB hg hquad x hx).contDiffAt
  have heq : (fun p => probedGradient (rfcMethod memory count) (A p) (B p) (c • g p) N)=fun p => c • Φ p :=
    funext fun p => (rfc_scalar memory count (A p) (B p) (g p) c hc.ne' N).1
  dsimp only
  rw [heq,taylorPolynomial_const_smul Φ k x h c hΦ,
    (rfc_scalar memory count (A (x+h)) (B (x+h)) (g (x+h)) c hc.ne' N).1,
    ← smul_sub,norm_smul,Real.norm_of_nonneg hc.le]
  exact (mul_le_mul_of_nonneg_left (hrem x hx h hh k hk hkr) hc.le).trans_eq (by ring)

end
end krylov.Stability
