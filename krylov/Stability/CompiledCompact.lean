import krylov.Methods.CompiledHomogeneous
import krylov.Methods.CompiledOutputs
import krylov.Stability.WeightedCompactTaylor
import krylov.Stability.HomogeneousTaylor
import krylov.Realization.ActualBudgetConversion

/-!
Article: main_krylov, lem:U(a,c,d) and prop:conv, genuine smooth-policy compact bounds.
Use: prove compact-uniform Taylor and unchanged positive-cone constants for
actual compiled CG-consistent methods, and quadratic canonical budget conversion
for their true total recorded steps, from primitive coefficient hypotheses.
Source: genuine compiled execution regularity, actual complete-history
homogeneity and the proved compact weighted integral Taylor and secant conversion theorems.
-/

namespace krylov.Stability
noncomputable section
open Set Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped Topology Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Actual compiled CG-consistent methods have genuine compact-uniform weighted Taylor remainders from primitive C-r coefficients.
Use: Actual compiled CG-consistent methods have genuine compact-uniform weighted Taylor remainders from primitive C-r coefficients.
Article: main_krylov, lem:U(a,c,d) and prop:conv, genuine smooth-policy compact bounds.
Proof: The actual quadratic query induction discharges search domains and proves real cycle regularity. The genuine finite-order smooth locus is open; apply the true compact weighted Taylor theorem there. -/
theorem compiledProbed_compact_taylor (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hconsistent : CGConsistent P.method)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ ∀ k<N, CG.gradient Q (g x) k≠0)
    (hcoef : ∀ x∈K, ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k))
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun p => probedGradient P.method (A p) (B p) (g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k*e x := by
  -- Derive actual smoothness from primitive coefficients before constructing the compact tube.
  let Φ := fun p => probedGradient P.method (A p) (B p) (g p) N
  have hΦ : ∀ x∈K, ContDiffAt ℝ r Φ x := by
    intro x hx
    obtain ⟨Q,hAx,hBx,hQ,hpos,hpre⟩ := hquad x hx
    exact P.gradient_regular A B g x N (P.quadratic_run_regular A B g x N (hA x hx) (hB x hx) (hg x hx)
      Q hAx hBx hQ hpos hconsistent hpre (hcoef x hx))
  let U := interior {x | ContDiffAt ℝ r Φ x}
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hΦ x hx).eventually (by simp))
  exact compact_weighted_taylor Φ e r U K isOpen_interior hK hsub
    (fun x hx => (show ContDiffAt ℝ r Φ x from interior_subset hx).contDiffWithinAt) he hepos


/-- The actual homogeneous compiled method has the same true compact Taylor constants and radius on its entire positive initial-gradient cone.
Use: The actual homogeneous compiled method has the same true compact Taylor constants and radius on its entire positive initial-gradient cone.
Article: main_krylov, lem:U(a,c,d) and prop:conv, genuine smooth-policy compact bounds.
Proof: Real complete-history homogeneity identifies the actual scaled output and all its genuine Taylor coefficients; scale the true compact remainder without changing its radius or constant. -/
theorem compiledProbed_compact_cone_taylor (P : CompiledProbedPolicy E) (hP : P.Homogeneous)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hconsistent : CGConsistent P.method)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ ∀ k<N, CG.gradient Q (g x) k≠0)
    (hcoef : ∀ x∈K, ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k))
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun c p => probedGradient P.method (A p) (B p) (c • g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ c : ℝ, 0<c → ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ c (x+h)-taylorPolynomial (Φ c) k x h‖≤C*‖h‖^k*(c*e x) := by
  -- True executed-method homogeneity retains the very same radius and remainder constant.
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compiledProbed_compact_taylor P A B g e N r K hK hA hB hg hconsistent hquad hcoef he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro c hc x hx h hh k hk hkr
  let F := fun p => probedGradient P.method (A p) (B p) (g p) N
  have hF : ContDiffAt ℝ k F x := by
    obtain ⟨Q,hAx,hBx,hQ,hpos,hpre⟩ := hquad x hx
    exact (P.gradient_regular A B g x N (P.quadratic_run_regular A B g x N (hA x hx) (hB x hx) (hg x hx)
      Q hAx hBx hQ hpos hconsistent hpre (hcoef x hx))).of_le (by exact_mod_cast hkr)
  have heq : (fun p => probedGradient P.method (A p) (B p) (c • g p) N)=fun p => c • F p :=
    funext fun p => P.gradient_scalar hP (A p) (B p) (g p) c hc N
  dsimp only
  rw [heq,taylorPolynomial_const_smul F k x h c hF,P.gradient_scalar hP _ _ _ c hc N,← smul_sub,norm_smul,Real.norm_of_nonneg hc.le]
  exact (mul_le_mul_of_nonneg_left (hbound x hx h hh k hk hkr) hc.le).trans_eq (by ring)

variable {n : ℕ}

/-- Every actual smooth compiled CG-consistent method has compact-uniform quadratic canonical budget conversion for its genuine total recorded steps.
Use: Every actual smooth compiled CG-consistent method has compact-uniform quadratic canonical budget conversion for its genuine total recorded steps.
Article: main_krylov, lem:U(a,c,d) and prop:conv, genuine smooth-policy compact bounds.
Proof: The real quadratic execution induction proves each actual step C-one from its true next history record. Apply the actual compact metric conversion with the genuine variable root and initial inverse-root error norm. -/
theorem compiledProbed_compact_secantConversion (P : CompiledProbedPolicy (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K) (hb : ContinuousOn base K)
    (hpos : ∀ x∈K, (base x).PosDef) (hgnz : ∀ x∈K, g x≠0)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ 1 g x)
    (hconsistent : CGConsistent P.method)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hpre : ∀ x∈K, ∀ k<N, CG.gradient (cgOperator (base x)) (g x) k≠0)
    (hcoef : ∀ x∈K, ∀ k<N, P.CoefficientsRegularAt 1 (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k))
    (hD : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (fun p => D p k) x) (hzero : ∀ x∈K, ∀ k<N, D x k=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖krylov.Realization.canonicalInjectionReplacement base
        (fun p => probedStep P.method (A p) (B p) (g p)) D x (x+h) j‖≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Each genuine step comes from the actual record produced by the next finite prefix.
  apply krylov.Realization.compact_metric_secantConversion base g _ D N K hK hb hpos
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hgnz _ hD hzero
  intro x hx i hi
  apply P.step_regular A B g x i
  exact P.quadratic_run_regular A B g x (i+1)
    (fun k hk => hA x hx k (by omega)) (fun k hk => hB x hx k (by omega)) (hg x hx)
    (cgOperator (base x)) (hAx x hx) (hBx x hx) (cgOperator_positive _ (hpos x hx)).1
    (cgOperator_positive _ (hpos x hx)).2 hconsistent (fun k hk => hpre x hx k (by omega))
    (fun k hk => hcoef x hx k (by omega))
end
end krylov.Stability
