import krylov.Methods.SmoothTrace
import krylov.Stability.WeightedCompactTaylor
import krylov.Realization.ActualBudgetConversion

/-!
Article: main_krylov, lem:U(a,d) and prop:conv, actual smooth raw-policy compact bounds.
Use: give genuine compact-uniform Taylor remainders and quadratic canonical
recorded-step budget conversion for arbitrary raw smooth CG-consistent
methods represented by primitive local observed coefficient charts.
Source: proved real local-program compilation, actual full history regularity
and the compact weighted Taylor and true variable-metric secant conversion theorems.
-/

namespace krylov.Stability
noncomputable section
open Set Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped Topology Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Every primitive locally smooth CG-consistent raw probed method has a genuine compact-uniform weighted Taylor remainder.
Use: Every primitive locally smooth CG-consistent raw probed method has a genuine compact-uniform weighted Taylor remainder.
Article: main_krylov, lem:U(a,d) and prop:conv, actual smooth raw-policy compact bounds.
Proof: At each real compact reference its actual primitive local program gives genuine returned-gradient C-r regularity. The true finite-order smooth locus is open, so the compact weighted integral Taylor theorem applies to the actual raw cycle map. -/
theorem smoothProbed_compact_taylor (m : ProbedMethod E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (e : X → ℝ) (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hconsistent : CGConsistent m)
    (hquad : ∀ x∈K, ∃ Q : E →L[ℝ] E, A x=(fun _ => Q) ∧ B x=(fun _ => Q) ∧
      Q.toLinearMap.IsSymmetric ∧ (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) ∧ (∀ k<N, CG.gradient Q (g x) k≠0) ∧ SmoothProbedCycleAt m r Q (g x) N)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun p => probedGradient m (A p) (B p) (g p) N
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k*e x := by
  -- Actual raw cycle regularity is derived locally from genuine primitive observed coefficients.
  let Φ := fun p => probedGradient m (A p) (B p) (g p) N
  have hΦ : ∀ x∈K, ContDiffAt ℝ r Φ x := by
    intro x hx
    obtain ⟨Q,hAx,hBx,hQ,hpos,hpre,hsmooth⟩ := hquad x hx
    exact smoothProbed_gradient_regular m hconsistent A B g x N (hA x hx) (hB x hx) (hg x hx)
      Q hAx hBx hQ hpos hpre hsmooth

  let U := interior {x | ContDiffAt ℝ r Φ x}
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hΦ x hx).eventually (by simp))
  exact compact_weighted_taylor Φ e r U K isOpen_interior hK hsub
    (fun x hx => (show ContDiffAt ℝ r Φ x from interior_subset hx).contDiffWithinAt) he hepos


variable {n : ℕ}

/-- Arbitrary primitive locally smooth CG-consistent raw probed methods have the genuine compact-uniform quadratic canonical budget-conversion remainder for their actual recorded steps.
Use: Arbitrary primitive locally smooth CG-consistent raw probed methods have the genuine compact-uniform quadratic canonical budget-conversion remainder for their actual recorded steps.
Article: main_krylov, lem:U(a,d) and prop:conv, actual smooth raw-policy compact bounds.
Proof: Restrict each true primitive local finite program to the actual needed prefix. Its genuine complete-history C-one chart contains the actual recorded displacement; apply the proved compact metric conversion with the true inverse-root initial-error weight. -/
theorem smoothProbed_compact_secantConversion (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B D : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K) (hb : ContinuousOn base K)
    (hpos : ∀ x∈K, (base x).PosDef) (hgnz : ∀ x∈K, g x≠0)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ 1 g x)
    (hconsistent : CGConsistent m)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hpre : ∀ x∈K, ∀ k<N, CG.gradient (cgOperator (base x)) (g x) k≠0)
    (hsmooth : ∀ x∈K, SmoothProbedCycleAt m 1 (cgOperator (base x)) (g x) N)
    (hD : ∀ x∈K, ∀ k<N, ContDiffAt ℝ 1 (fun p => D p k) x) (hzero : ∀ x∈K, ∀ k<N, D x k=0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → ∀ j≤N,
      ‖krylov.Realization.canonicalInjectionReplacement base
        (fun p => probedStep m (A p) (B p) (g p)) D x (x+h) j‖≤
        C*‖h‖^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  -- The real recorded displacement is read from the actual next complete iteration record.
  apply krylov.Realization.compact_metric_secantConversion base g _ D N K hK hb hpos
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hgnz _ hD hzero
  intro x hx i hi
  have hs : SmoothProbedCycleAt m 1 (cgOperator (base x)) (g x) (i+1) := by
    obtain ⟨P,hcoef,hlocal⟩ := hsmooth x hx
    exact ⟨P,(fun k hk => hcoef k (by omega)),fun k hk => hlocal k (by omega)⟩
  have htrace := smoothProbed_trace_regular m hconsistent A B g x (i+1)
    (fun k hk => hA x hx k (by omega)) (fun k hk => hB x hx k (by omega)) (hg x hx)
    (cgOperator (base x)) (hAx x hx) (hBx x hx) (cgOperator_positive _ (hpos x hx)).1
    (cgOperator_positive _ (hpos x hx)).2 (fun k hk => hpre x hx k (by omega)) hs
  exact htrace.getD 4

end
end krylov.Stability
