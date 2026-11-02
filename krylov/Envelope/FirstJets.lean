import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-!
Article: main_krylov, apB:lem:filtration, actual observed first-derivative calculus.
Use: separate coefficient-derivative terms inside the real reference Krylov
span and eliminate unknown correction-operator derivatives on true zero
reference queries. These are primitive lemmas for the actual execution induction.
Source: Mathlib.Analysis.Calculus.Deriv.Mul and FDeriv.CompCLM, the proved
finite sum, scalar product and continuous-linear evaluation product rules.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The genuine derivative of a finite smooth observed-vector combination.
Use: The genuine derivative of a finite smooth observed-vector combination.
Article: main_krylov, apB:lem:filtration, actual observed first-derivative calculus.
Proof: Apply the actual scalar-vector product rule termwise and the finite sum rule. -/
theorem hasDerivAt_observedCombination (c : ι → ℝ → ℝ) (v : ι → ℝ → E)
    (dc : ι → ℝ) (dv : ι → E) (t : ℝ) (hc : ∀ i, HasDerivAt (c i) (dc i) t)
    (hv : ∀ i, HasDerivAt (v i) (dv i) t) :
    HasDerivAt (fun x => ∑ i, c i x • v i x) (∑ i, (c i t • dv i+dc i • v i t)) t := by
  convert HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hc i).smul (hv i)) using 1
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply']

/-- Coefficient derivatives in a genuine observed linear combination remain inside its actual reference subspace.
Use: Coefficient derivatives in a genuine observed linear combination remain inside its actual reference subspace.
Article: main_krylov, apB:lem:filtration, actual observed first-derivative calculus.
Proof: Split the true derivative into its fixed-coefficient vector derivative and the sum of coefficient derivatives times genuine reference vectors. -/
theorem combination_derivative_mod (K : Submodule ℝ E) (c : ι → ℝ → ℝ) (v : ι → ℝ → E)
    (dc : ι → ℝ) (dv : ι → E) (t : ℝ) (hc : ∀ i, HasDerivAt (c i) (dc i) t)
    (hv : ∀ i, HasDerivAt (v i) (dv i) t) (hK : ∀ i, v i t∈K) :
    deriv (fun x => ∑ i, c i x • v i x) t-(∑ i, c i t • dv i)∈K := by
  rw [(hasDerivAt_observedCombination c v dc dv t hc hv).deriv,Finset.sum_add_distrib,add_sub_cancel_left]
  exact K.sum_mem fun i _ => K.smul_mem (dc i) (hK i)

/-- The real oracle action has the actual operator/vector product derivative.
Use: The real oracle action has the actual operator/vector product derivative.
Article: main_krylov, apB:lem:filtration, actual observed first-derivative calculus.
Proof: Use the continuous-linear evaluation product rule. -/
theorem operator_jet_action (A : ℝ → E →L[ℝ] E) (v : ℝ → E)
    (dA : E →L[ℝ] E) (dv : E) (t : ℝ)
    (hA : HasDerivAt A dA t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun x => A x (v x)) (A t dv+dA (v t)) t := by
  simpa only [add_comm] using hA.clm_apply hv

/-- The derivative of a genuine zero reference correction query is independent of the correction-operator derivative.
Use: The derivative of a genuine zero reference correction query is independent of the correction-operator derivative.
Article: main_krylov, apB:lem:filtration, actual observed first-derivative calculus.
Proof: In the true product rule, that derivative acts on the actual zero reference displacement. -/
theorem zero_query_jet (A : ℝ → E →L[ℝ] E) (v : ℝ → E)
    (dA : E →L[ℝ] E) (dv : E) (t : ℝ)
    (hA : HasDerivAt A dA t) (hv : HasDerivAt v dv t) (hz : v t=0) :
    HasDerivAt (fun x => A x (v x)) (A t dv) t := by
  simpa only [hz,map_zero,add_zero] using operator_jet_action A v dA dv t hA hv
end
end krylov.Envelope
