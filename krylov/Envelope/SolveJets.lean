import krylov.Envelope.JetSubspace
import krylov.Stability.ContDiffSolve
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual observed finite-solve jet closure.
Use: propagate genuine virtual correction and conjugacy direction first jets through the actual smooth coefficient solves on their true matrix domains.
Source: the proved C-one native model and conjugacy coefficients and genuine observed scalar-vector jet closure.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- The true finite inverse-model correction inherits the actual first-jet coherence of its genuine moving physical step vectors.
Use: The true finite inverse-model correction inherits the actual first-jet coherence of its genuine moving physical step vectors.
Article: main_krylov, thm:E1, actual observed finite-solve jet closure.
Proof: Differentiate the actual smooth native coefficient combination on its genuine nonzero determinant domain. -/
theorem model_solve_jet (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (S : ℝ → Fin p → E) (M : ℝ → Matrix (Fin p) (Fin p) ℝ) (g : ℝ → E)
    (hS : ∀ i,ContDiffAt ℝ 1 (fun t => S t i) 0)
    (hM : ∀ i j,ContDiffAt ℝ 1 (fun t => M t i j) 0) (hg : ContDiffAt ℝ 1 g 0)
    (hdet : (M 0).det≠0) (hj : ∀ i,(S 0 i,deriv (fun t => S t i) 0)∈jetSubspace K L) :
    (combine (S 0) (modelCoefficients (S 0) (M 0) (g 0)),
      deriv (fun t => combine (S t) (modelCoefficients (S t) (M t) (g t))) 0)∈jetSubspace K L := by
  have hc := contDiff_modelCoefficients S M g 0 hS hM hg hdet
  exact observed_combination_jet K L (fun i t => modelCoefficients (S t) (M t) (g t) i)
    (fun i t => S t i) (fun i => deriv (fun t => modelCoefficients (S t) (M t) (g t) i) 0)
    (fun i => deriv (fun t => S t i) 0) 0
    (fun i => ((hc i).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hS i).differentiableAt (by norm_num)).hasDerivAt) hj

/-- The true computed conjugacy direction inherits genuine first-jet coherence from its actual gradient and moving stored physical steps.
Use: The true computed conjugacy direction inherits genuine first-jet coherence from its actual gradient and moving stored physical steps.
Article: main_krylov, thm:E1, actual observed finite-solve jet closure.
Proof: Use the actual smooth conjugacy coefficients and finite observed-combination closure, then add the genuine negative gradient jet. -/
theorem conjugacy_solve_jet (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (S Y : ℝ → Fin p → E) (g : ℝ → E)
    (hS : ∀ i,ContDiffAt ℝ 1 (fun t => S t i) 0)
    (hY : ∀ i,ContDiffAt ℝ 1 (fun t => Y t i) 0) (hg : ContDiffAt ℝ 1 g 0)
    (hdet : (crossGram (Y 0) (S 0)).det≠0)
    (hj : ∀ i,(S 0 i,deriv (fun t => S t i) 0)∈jetSubspace K L)
    (hgj : (g 0,deriv g 0)∈jetSubspace K L) :
    (conjugacyDirection (S 0) (Y 0) (g 0),
      deriv (fun t => conjugacyDirection (S t) (Y t) (g t)) 0)∈jetSubspace K L := by
  -- Only true scalar coefficient derivatives are discarded into the genuine physical reference flag.
  have hc := contDiff_conjugacyCoefficients S Y g 0 hS hY hg hdet
  have hh := observed_combination_jet K L (fun i t => conjugacyCoefficients (S t) (Y t) (g t) i)
    (fun i t => S t i) (fun i => deriv (fun t => conjugacyCoefficients (S t) (Y t) (g t) i) 0)
    (fun i => deriv (fun t => S t i) 0) 0
    (fun i => ((hc i).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hS i).differentiableAt (by norm_num)).hasDerivAt) hj
  have hcomb := contDiff_combine S _ 0 hS hc
  have hd := (hg.differentiableAt (by norm_num)).hasDerivAt.neg.add (hcomb.differentiableAt (by norm_num)).hasDerivAt
  change HasDerivAt (fun t => conjugacyDirection (S t) (Y t) (g t)) _ 0 at hd
  rw [hd.deriv]
  simpa only [conjugacyDirection,combine,Prod.mk_add_mk,Prod.neg_mk] using
    (jetSubspace K L).add_mem ((jetSubspace K L).neg_mem hgj) hh
end
end krylov.Envelope
