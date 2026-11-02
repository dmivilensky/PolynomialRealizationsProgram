import krylov.OneGradient.CompletionCG
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), original physical known-prior base family.
Use: realize the source's last-Lanczos positive base perturbation with
its exact original prior budget and genuine complete CG information.
Source: the already proved whole physical last-pivot fibre, exact
rank-one relative norm and real reciprocal final CG length.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant
variable {n : ℕ}

/-- The actual source known-prior base perturbation along the genuine
last physical Lanczos normal, normalized by the actual last CG length.
Use: at rho=c*omega this is precisely the original physical attaining
family A+(c*omega/alpha_last) zzᵀ, defined before any canonical model.
Article: main_krylov, thm:local(b), true prior-attaining physical base. -/
def informedPriorBase (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  lanczosCompletion A hA g hg hc
    (lastJacobiPivot A hA g hg hc+rho/lastInversePivot A hA g hg hc)

/-- Every nonnegative true prior radius gives a genuine positive
physical reference in the source's actual last-Lanczos fibre.
Use: all physical inverse domains are derived for the attaining family.
Article: main_krylov, thm:local(b), true positive base family.
Proof: the original whole-fibre threshold is strictly below the original
pivot, whereas the actual nonnegative normalized displacement is above it. -/
theorem informedPriorBase_posDef
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤ rho) :
    (informedPriorBase A hA g hg hc rho).PosDef := by
  rw [informedPriorBase,lanczos_completion_positive_iff]
  have hp := last_inverse_pivot_positive A hA g hg hc
  have hi := inv_pos.mpr hp
  have hd := div_nonneg hrho hp.le
  linarith

/-- The actual physical base family spends exactly its original known
relative-base prior radius, including zero radius.
Use: the original sharpness family satisfies the true physical prior,
rather than an assumed or first-order surrogate canonical budget.
Article: main_krylov, thm:local(b), exact original prior budget.
Proof: the true rank-one relative norm is the absolute physical scalar
times the genuine last inverse pivot; cancel its proved positive value. -/
theorem informedPriorBase_budget
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤ rho) :
    relativeBudget A (informedPriorBase A hA g hg hc rho-A)=rho := by
  have hp := last_inverse_pivot_positive A hA g hg hc
  rw [informedPriorBase,lanczosCompletion,add_sub_cancel_left,add_sub_cancel_left,rank_one_relative_budget A hA]
  change |rho/lastInversePivot A hA g hg hc| *lastInversePivot A hA g hg hc=rho
  rw [abs_of_nonneg (div_nonneg hrho hp.le),div_mul_cancel₀ _ hp.ne']

/-- The source prior-attaining physical base retains every real active
CG atom and hence all genuine complete reference inverse domains.
Use: no full-support or nonstagnation assumption is added to the new base.
Article: main_krylov, thm:local(b), actual full-atom perturbed reference.
Proof: every positive point of the genuine physical last-pivot fibre has
the original full atom count; positivity has already been derived. -/
theorem informedPriorBase_full_atoms
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤ rho) :
    referenceAtomCount (informedPriorBase A hA g hg hc rho)
      (informedPriorBase_posDef A hA g hg hc rho hrho) g=n+1 :=
  completion_full_atoms A hA g hg hc _ (informedPriorBase_posDef A hA g hg hc rho hrho)

/-- Every real CG state through the last unqueried direction is exactly
unchanged along the original physical prior-attaining family.
Use: the known-base informed trial calibrates to the same true last
direction before the unknown prior displacement is measured.
Article: main_krylov, thm:local(b), genuine common prior information.
Proof: the family belongs to the actual physical last-Lanczos fibre. -/
theorem informedPriorBase_cg_prefix
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (k : ℕ) (hk : k≤ n) :
    cgRun (cgOperator (informedPriorBase A hA g hg hc rho)) g k=cgRun (cgOperator A) g k :=
  completion_cg_prefix A hA g hg hc _ k hk

/-- The genuine final CG length on the original physical prior family
is exactly the known last length divided by one plus the prior radius.
Use: the true canonical prior coefficient is rho/(1+rho), with the
original c*omega leading coefficient and a genuine quadratic loss.
Article: main_krylov, thm:local(b), exact actual last length.
Proof: substitute the actual prior pivot in the already proved physical
completion last-length formula. Its real inverse pivot is the original
CG length, so exact positive-denominator algebra gives the result. -/
theorem informedPriorBase_last_length
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤ rho) :
    CG.length (cgOperator (informedPriorBase A hA g hg hc rho)) g n=
      CG.length (cgOperator A) g n/(1+rho) := by
  have hp := last_inverse_pivot_positive A hA g hg hc
  rw [informedPriorBase,completion_last_cg_length,add_sub_cancel_left,
    ← last_inverse_pivot_cg_length A hA g hg hc]
  field_simp
  ring

end
end krylov.OneGradient
