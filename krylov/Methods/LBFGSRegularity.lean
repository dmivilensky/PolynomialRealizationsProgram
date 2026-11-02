import krylov.Methods.LBFGSReference
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, cor:lm and s3:cor:qn, real primitive BFGS/L-BFGS regularity.
Use: derive smoothness of the actual finite observed two-loop decision from
its genuine observed inner-product coefficients and actual nonzero curvature
pivots, without a presumed smooth cycle map.
Source: classical two-loop inverse-BFGS recursion and mathlib finite-product,
inner-product, reciprocal and scalar-vector C-r calculus.
-/

namespace krylov.Methods
noncomputable section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {r : WithTop ℕ∞}

/-- The genuine finite inverse-BFGS two-loop decision has every stated differentiability order on its actual nonzero observed curvature domain.
Use: The genuine finite inverse-BFGS two-loop decision has every stated differentiability order on its actual nonzero observed curvature domain.
Article: main_krylov, cor:lm and s3:cor:qn, real primitive BFGS/L-BFGS regularity.
Proof: Induct on the real retained-pair array. Prove each actual backward coefficient, recursively computed vector and true forward coefficient smooth before combining the actual physical output. -/
theorem inverseBFGSApply_contDiffAt {N : ℕ} (w : X → Fin N → E × E) (c : X → ℝ)
    (v : X → E) (x : X) (hw : ∀ i, ContDiffAt ℝ r (fun p => w p i) x)
    (hc : ContDiffAt ℝ r c x) (hv : ContDiffAt ℝ r v x)
    (hpiv : ∀ i, inner ℝ (w x i).1 (w x i).2≠0) :
    ContDiffAt ℝ r (fun p => inverseBFGSApply (c p) (List.ofFn (w p)) (v p)) x := by
  -- Prove smoothness of every real scalar decision on its genuine pivot domain before evaluating its physical vector update.
  induction N generalizing v with
  | zero =>
    simp only [List.ofFn_zero,inverseBFGSApply]
    convert hc.smul hv using 1
  | succ N ih =>
    let s := fun p => (w p 0).1
    let y := fun p => (w p 0).2
    let ρ := fun p => (inner ℝ (s p) (y p))⁻¹
    let a := fun p => ρ p*inner ℝ (s p) (v p)
    have hs : ContDiffAt ℝ r s x := (hw 0).fst
    have hy : ContDiffAt ℝ r y x := (hw 0).snd
    have hρ : ContDiffAt ℝ r ρ x := (hs.inner ℝ hy).inv (hpiv 0)
    have ha : ContDiffAt ℝ r a x := hρ.mul (hs.inner ℝ hv)
    have hr := ih (fun p i => w p i.succ) (fun p => v p-a p • y p)
      (fun i => hw i.succ) (hv.sub (ha.smul hy)) (fun i => hpiv i.succ)
    have hβ := ha.sub (hρ.mul (hy.inner ℝ hr))
    have h := hr.add (hβ.smul hs)
    convert h using 1
    funext p
    rw [List.ofFn_succ]
    rfl
end
end krylov.Methods
