import krylov.OneGradient.InformedPriorCanonical
import krylov.Information.MetricSlack
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), exact physical prior in the known frame.
Use: construct physical sharpness scenarios using fixed known canonical
attainers while respecting every true perturbed-base increment budget.
Source: genuine last-Lanczos physical fibre, actual canonical normal
transport and the existing Loewner relative-budget transfer theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.LinearAlgebra krylov.Information
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual last-Lanczos prior has exactly coefficient rho in the
fixed known canonical last-CG axis, with no alignment remainder.
Use: fixed canonical sharpness witnesses lift directly to actual physical
source scenarios with the genuine known-base prior.
Article: main_krylov, thm:local(b), exact known-frame physical prior.
Proof: the real original penultimate gradient is its actual unit Lanczos
normal times a nonzero scalar. Apply true last-normal canonical transport
at the known base and cancel its genuine positive final CG length. -/
theorem informedPriorBase_known_canonical_form
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) :
    cgOperator (relativeOperator A (informedPriorBase A hA g hg hc rho-A))=
      rho • InnerProductSpace.rankOne ℝ (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n) := by
  let z := lastLanczosVector A hA g hg hc
  let alpha := lastInversePivot A hA g hg hc
  have hcount : referenceAtomCount A hA g=n+1 := full_gradient_atom_count A hA g hc
  obtain ⟨hgrad,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  have hform := canonical_last_normal_form A hA g hcount z (last_lanczos_unit A hA g hg hc)
    (inner ℝ z (CG.gradient (cgOperator A) g n)) (rho/alpha) hgamma hgrad
  have hdiff : informedPriorBase A hA g hg hc rho-A=
      (rho/alpha) • vecMulVec (WithLp.ofLp z) (WithLp.ofLp z) := by
    simp only [informedPriorBase,lanczosCompletion,add_sub_cancel_left]
    rfl
  rw [hdiff,hform,← last_inverse_pivot_cg_length A hA g hg hc]
  dsimp only [alpha]
  rw [div_mul_cancel₀ _ (last_inverse_pivot_positive A hA g hg hc).ne']

/-- Every nonnegative original physical prior base dominates the known
base in the true Loewner order.
Use: fixed known-metric canonical increments spend no more budget when
measured in the actual perturbed-base metric.
Article: main_krylov, thm:local(b), real prior base domination.
Proof: the actual prior displacement is a nonnegative multiple of the
genuine physical last-normal rank-one positive semidefinite matrix. -/
theorem informedPriorBase_domination
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤rho) :
    A ≤ informedPriorBase A hA g hg hc rho := by
  rw [Matrix.le_iff]
  simp only [informedPriorBase,lanczosCompletion,add_sub_cancel_left]
  simpa only [star_trivial] using
    (Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp (lastLanczosVector A hA g hg hc))).smul
      (div_nonneg hrho (last_inverse_pivot_positive A hA g hg hc).le)

/-- Every true known-base symmetric perturbation budget remains valid
in the actual positive prior base, including zero budgets and radius.
Use: the original attaining physical family needs no artificial shrinking
of its canonical increment or independent output witnesses.
Article: main_krylov, thm:local(b), exact physical sharpness budgets.
Proof: reuse the proved real Loewner budget transfer with factor one and
the genuine prior base domination and derived positivity. -/
theorem informedPriorBase_budget_transfer
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤rho)
    (E : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hE : E.IsSymm) (w : ℝ) (hw : 0≤w)
    (hbudget : relativeBudget A E≤w) :
    relativeBudget (informedPriorBase A hA g hg hc rho) E≤w := by
  have h := relative_budget_change A (informedPriorBase A hA g hg hc rho) E hA
    (informedPriorBase_posDef A hA g hg hc rho hrho) hE (by norm_num : (0 : ℝ)≤1) hw
    (by simpa only [one_smul] using informedPriorBase_domination A hA g hg hc rho hrho)
    (by simpa only [one_mul] using hbudget)
  exact h

end
end krylov.OneGradient
