import krylov.Stability.FCCompactRemainder
import krylov.Stability.HomogeneousTaylor
import krylov.Methods.HomogeneousFC

/-!
Article: main_krylov, lem:U(c,d), genuine FC compact cones.
Use: apply the actual executed FC scaling theorem to extend compact weighted
Taylor remainders to every positive scale with exactly the same constants.
Source: the proved actual FC homogeneity, actual quadratic analytic domains,
and finite Taylor polynomial covariance under constant scalar multiplication.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Actual full-memory FC has the same compact Taylor constants on the entire positive initial-gradient cone.
Use: all regularity and homogeneity premises are proved for the true FC policy, rather than supplied as an abstract expansion.
Article: main_krylov, lem:U(c,d), actual FC cone estimate.
Proof: actual quadratic CG domains give actual analytic regularity at every
reference. The compact FC theorem supplies one radius and constant. The actual
FC trajectory scales exactly, so its genuine finite Taylor polynomial and
remainder scale by the same positive factor, leaving both constants unchanged. -/
theorem quadraticFC_compact_cone_taylor (A : X → ℕ → E →L[ℝ] E) (g : X → E)
    (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ i, AnalyticAt ℝ (fun p => A p i) x)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ Q.toLinearMap.IsSymmetric ∧
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ ∀ i<N, CG.gradient Q (g x) i≠0)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ∀ c : ℝ, 0<c →
      let Φc := fun p => fcGradient fullMemory (A p) (c • g p) N
      ‖Φc (x+h)-taylorPolynomial Φc k x h‖≤C*‖h‖^k*(c*e x) := by
  -- Use one genuine compact estimate before introducing any positive initial-gradient scale.
  obtain ⟨δ,C,hδ,hC,hrem⟩ := quadraticFC_compact_weighted_taylor A g e N r K hK hA hg hquad he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh k hk hkr c hc
  let Φ := fun p => fcGradient fullMemory (A p) (g p) N
  have hΦ : ContDiffAt ℝ k Φ x := by
    obtain ⟨Q,hAx,hQ,hpos,hpre⟩ := hquad x hx
    exact (quadraticFC_prefix_analytic A g x (hA x hx) (hg x hx) Q hAx hQ hpos N hpre).1.contDiffAt
  have heq : (fun p => fcGradient fullMemory (A p) (c • g p) N)=fun p => c • Φ p :=
    funext fun p => (fullFC_scalar (A p) (g p) c hc.ne' N).1
  dsimp only
  rw [heq,taylorPolynomial_const_smul Φ k x h c hΦ,
    (fullFC_scalar (A (x+h)) (g (x+h)) c hc.ne' N).1,
    ← smul_sub,norm_smul,Real.norm_of_nonneg hc.le]
  exact (mul_le_mul_of_nonneg_left (hrem x hx h hh k hk hkr) hc.le).trans_eq (by ring)

end
end krylov.Stability
