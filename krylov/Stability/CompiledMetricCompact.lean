import krylov.Stability.CompiledCompact
import krylov.Stability.MetricRootRegularity

/-!
Article: main_krylov, lem:U(a,d), genuine canonical smooth-policy compact Taylor bounds.
Use: give actual compact-uniform Taylor remainders of the real canonical
compiled method output with the true varying inverse-root initial-error factor.
Source: genuine primitive-coefficient execution regularity, proved actual
variable positive root/inverse-root C-r calculus and the compact weighted Taylor theorem.
-/

namespace krylov.Stability
noncomputable section
open Set Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The actual canonical output of every primitive smooth compiled CG-consistent method has the printed compact-uniform weighted Taylor remainder with its genuine variable metric.
Use: The actual canonical output of every primitive smooth compiled CG-consistent method has the printed compact-uniform weighted Taylor remainder with its genuine variable metric.
Article: main_krylov, lem:U(a,d), genuine canonical smooth-policy compact Taylor bounds.
Proof: The real quadratic execution theorem derives actual gradient regularity and discharges genuine search domains. Compose the actual varying inverse root, then use the true positive continuous canonical initial-error norm in the compact integral Taylor theorem. -/
theorem compiledProbed_metric_compact_taylor (P : CompiledProbedPolicy (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ r base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hgnz : ∀ x∈K, g x≠0)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hconsistent : CGConsistent P.method)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hpre : ∀ x∈K, ∀ k<N, CG.gradient (cgOperator (base x)) (g x) k≠0)
    (hcoef : ∀ x∈K, ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k)) :
    let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (probedGradient P.method (A p) (B p) (g p) N)
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤
        C*‖h‖^k*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Both the actual trajectory and true variable metric are derived from primitive smooth data.
  let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
    (probedGradient P.method (A p) (B p) (g p) N)
  have hbasepos : ∀ x∈K, (base x).PosDef := fun x hx => (hpos x hx).self_of_nhds
  -- Genuine root regularity closes the joint reference/perturbation dependence of the canonical output.
  have hΦ : ∀ x∈K, ContDiffAt ℝ r Φ x := by
    intro x hx
    have htrace := P.quadratic_run_regular A B g x N (hA x hx) (hB x hx) (hg x hx)
      (cgOperator (base x)) (hAx x hx) (hBx x hx) (cgOperator_positive _ (hbasepos x hx)).1
      (cgOperator_positive _ (hbasepos x hx)).2 hconsistent (hpre x hx) (hcoef x hx)
    exact (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (hb x hx) (hpos x hx))).clm_apply
      (P.gradient_regular A B g x N htrace)
  let U := interior {x | ContDiffAt ℝ r Φ x}
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hΦ x hx).eventually (by simp))
  apply compact_weighted_taylor Φ _ r U K isOpen_interior hK hsub
    (fun x hx => (show ContDiffAt ℝ r Φ x from interior_subset hx).contDiffWithinAt)
  · exact canonical_error_continuousOn base g K
      (fun x hx => (hb x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hbasepos
  · exact fun x hx => canonical_error_pos (base x) (hbasepos x hx) (g x) (hgnz x hx)
end
end krylov.Stability
