import krylov.Stability.SmoothCompact
import krylov.Stability.MetricRootRegularity

/-!
Article: main_krylov, lem:U, actual raw-method compact canonical regularity.
Use: give one genuine compact Taylor tube for an arbitrary locally smooth
CG-consistent raw method, with its varying physical metric and actual
inverse-root initial-error weight, deriving every regularity premise.
Source: the actual primitive-policy execution theorem, genuine CFC inverse-root
regularity and the proved compact weighted integral Taylor theorem.
-/

namespace krylov.Stability
noncomputable section
open Set Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- Every actual smooth CG-consistent raw method has compact-uniform canonical Taylor remainders with the genuine varying positive metric and actual initial-error factor.
Use: Every actual smooth CG-consistent raw method has compact-uniform canonical Taylor remainders with the genuine varying positive metric and actual initial-error factor.
Article: main_krylov, lem:U, actual raw-method compact canonical regularity.
Proof: Primitive local observed programs give actual raw-gradient regularity. The genuine variable-base inverse root is regular on the actual positive domain; apply the compact weighted Taylor theorem with its proved positive continuous reference-error weight. -/
theorem smoothProbed_metric_compact_taylor (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N r : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, ContDiffAt ℝ r base x) (hpos : ∀ x∈K, ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hgnz : ∀ x∈K, g x≠0)
    (hA : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ x∈K, ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ∀ x∈K, ContDiffAt ℝ r g x)
    (hconsistent : CGConsistent m)
    (hAx : ∀ x∈K, A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K, B x=fun _ => cgOperator (base x))
    (hpre : ∀ x∈K, ∀ k<N, CG.gradient (cgOperator (base x)) (g x) k≠0)
    (hsmooth : ∀ x∈K, SmoothProbedCycleAt m r (cgOperator (base x)) (g x) N) :
    let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (probedGradient m (A p) (B p) (g p) N)
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤
        C*‖h‖^k*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Differentiate the genuine varying-metric executed output before choosing its common compact tube.
  let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
    (probedGradient m (A p) (B p) (g p) N)
  have hbasepos : ∀ x∈K, (base x).PosDef := fun x hx => (hpos x hx).self_of_nhds
  have hΦ : ∀ x∈K, ContDiffAt ℝ r Φ x := by
    intro x hx
    have hG := smoothProbed_gradient_regular m hconsistent A B g x N (hA x hx) (hB x hx) (hg x hx)
      (cgOperator (base x)) (hAx x hx) (hBx x hx) (cgOperator_positive _ (hbasepos x hx)).1
      (cgOperator_positive _ (hbasepos x hx)).2 (hpre x hx) (hsmooth x hx)
    exact (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (hb x hx) (hpos x hx))).clm_apply hG

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
