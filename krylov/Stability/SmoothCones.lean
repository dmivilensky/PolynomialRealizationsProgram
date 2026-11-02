import krylov.Stability.SmoothCompact
import krylov.Methods.HomogeneousProtocol
import krylov.Stability.HomogeneousTaylor

/-!
Article: main_krylov, lem:U(c,d), genuine raw smooth-method compact cones.
Use: extend actual compact-uniform Taylor constants unchanged to all positive
initial-gradient scalings of arbitrary raw smooth CG-consistent probed methods.
Source: true primitive decision homogeneity, genuine local finite coefficient
compilation, actual real execution scaling and the compact weighted Taylor theorem.
-/

namespace krylov.Stability
noncomputable section
open Set krylov.Methods krylov.Reference
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Every actual primitive homogeneous smooth CG-consistent raw probed method has the same compact Taylor constants and radius on its genuine positive initial-gradient cone.
Use: Every actual primitive homogeneous smooth CG-consistent raw probed method has the same compact Taylor constants and radius on its genuine positive initial-gradient cone.
Article: main_krylov, lem:U(c,d), genuine raw smooth-method compact cones.
Proof: Obtain the real compact weighted Taylor bound from primitive local observed coefficient charts. True raw decision-tree homogeneity scales the complete actual execution and its genuine Taylor coefficients, preserving the same constants and radius. -/
theorem smoothProbed_compact_cone_taylor (m : ProbedMethod E) (hP : m.Homogeneous)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hconsistent : CGConsistent m)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ (∀ k<N, CG.gradient Q (g x) k≠0) ∧ SmoothProbedCycleAt m r Q (g x) N)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun c p => probedGradient m (A p) (B p) (c • g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ c : ℝ, 0<c → ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ c (x+h)-taylorPolynomial (Φ c) k x h‖≤C*‖h‖^k*(c*e x) := by
  -- Preserve the real compact constants while scaling the actual executed raw method, rather than an assumed cycle map.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := smoothProbed_compact_taylor m A B g e N r K hK hA hB hg hconsistent hquad he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro c hc x hx h hh k hk hkr
  let F := fun p => probedGradient m (A p) (B p) (g p) N
  have hF : ContDiffAt ℝ k F x := by
    obtain ⟨Q,hAx,hBx,hQ,hpos,hpre,hsmooth⟩ := hquad x hx
    exact (smoothProbed_gradient_regular m hconsistent A B g x N (hA x hx) (hB x hx) (hg x hx)
      Q hAx hBx hQ hpos hpre hsmooth).of_le (by exact_mod_cast hkr)

  have heq : (fun p => probedGradient m (A p) (B p) (c • g p) N)=fun p => c • F p :=
    funext fun p => probedGradient_scalar m hP (A p) (B p) (g p) c hc N
  dsimp only
  rw [heq,taylorPolynomial_const_smul F k x h c hF,probedGradient_scalar m hP _ _ _ c hc N,← smul_sub,norm_smul,Real.norm_of_nonneg hc.le]
  exact (mul_le_mul_of_nonneg_left (hbound x hx h hh k hk hkr) hc.le).trans_eq (by ring)

end
end krylov.Stability
