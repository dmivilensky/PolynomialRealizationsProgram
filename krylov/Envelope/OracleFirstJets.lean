import krylov.Methods.FiniteOracleCharts
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual finite oracle first-jet transfer.
Use: transfer true actual raw-method gradient first derivatives between
genuine finite operator paths sharing the same real first jets, after
primitive smooth policy membership has derived actual cycle regularity.
Source: genuine finite operator-coordinate execution and the standard
Frechet chain rule; no response equality is assumed.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Reference
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The genuine finite line and correction operator-coordinate path has exactly its true coordinatewise derivative.
Use: The genuine finite line and correction operator-coordinate path has exactly its true coordinatewise derivative.
Article: main_krylov, apB:lem:mu(c), actual finite oracle first-jet transfer.
Proof: Assemble the actual finite operator derivative arrays and their genuine product derivative. -/
theorem finiteOracle_path_hasDeriv (A B : ℝ → ℕ → E →L[ℝ] E) (dA dB : ℕ → E →L[ℝ] E) (N : ℕ)
    (hA : ∀ i<N, HasDerivAt (fun t => A t i) (dA i) 0)
    (hB : ∀ i<N, HasDerivAt (fun t => B t i) (dB i) 0) :
    HasDerivAt (fun t => ((fun i : Fin N => A t i.val),(fun i : Fin N => B t i.val)))
      ((fun i : Fin N => dA i.val),(fun i : Fin N => dB i.val)) 0 :=
  (hasDerivAt_pi.mpr (fun i : Fin N => hA i.val i.isLt)).prodMk
    (hasDerivAt_pi.mpr (fun i : Fin N => hB i.val i.isLt))

/-- Every genuinely differentiable finite observed-operator output has the same true derivative on actual operator paths with equal reference values and real first jets.
Use: Every genuinely differentiable finite observed-operator output has the same true derivative on actual operator paths with equal reference values and real first jets.
Article: main_krylov, apB:lem:mu(c), actual finite oracle first-jet transfer.
Proof: Compose the actual Frechet derivative with each true finite operator path derivative; their genuine reference inputs and real tangent arrays agree exactly. -/
theorem finiteOracle_firstJet_transfer (Q : E →L[ℝ] E) (N : ℕ)
    (f : ((Fin N → E →L[ℝ] E) × (Fin N → E →L[ℝ] E)) → F)
    (hf : DifferentiableAt ℝ f ((fun _ => Q),(fun _ => Q)))
    (A B A' B' : ℝ → ℕ → E →L[ℝ] E) (dA dB : ℕ → E →L[ℝ] E)
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hA0' : A' 0=fun _ => Q) (hB0' : B' 0=fun _ => Q)
    (hA : ∀ i<N, HasDerivAt (fun t => A t i) (dA i) 0)
    (hB : ∀ i<N, HasDerivAt (fun t => B t i) (dB i) 0)
    (hA' : ∀ i<N, HasDerivAt (fun t => A' t i) (dA i) 0)
    (hB' : ∀ i<N, HasDerivAt (fun t => B' t i) (dB i) 0) :
    deriv (fun t => f ((fun i : Fin N => A t i.val),(fun i : Fin N => B t i.val))) 0=
      deriv (fun t => f ((fun i : Fin N => A' t i.val),(fun i : Fin N => B' t i.val))) 0 := by
  -- The genuine operator paths have the same actual tangent array at the true finite reference input.
  have hp := finiteOracle_path_hasDeriv A B dA dB N hA hB
  have hp' := finiteOracle_path_hasDeriv A' B' dA dB N hA' hB'
  have hf1 : HasFDerivAt f (fderiv ℝ f ((fun _ => Q),(fun _ => Q)))
      ((fun i : Fin N => A 0 i.val),(fun i : Fin N => B 0 i.val)) := by
    rw [hA0,hB0]
    exact hf.hasFDerivAt
  have hf2 : HasFDerivAt f (fderiv ℝ f ((fun _ => Q),(fun _ => Q)))
      ((fun i : Fin N => A' 0 i.val),(fun i : Fin N => B' 0 i.val)) := by
    rw [hA0',hB0']
    exact hf.hasFDerivAt
  exact (hf1.comp_hasDerivAt 0 hp).deriv.trans (hf2.comp_hasDerivAt 0 hp').deriv.symm

/-- Actual primitive smooth globally CG-consistent raw-method gradients have identical genuine first derivatives on true line and correction operator paths with the same actual finite first jets.
Use: Actual primitive smooth globally CG-consistent raw-method gradients have identical genuine first derivatives on true line and correction operator paths with the same actual finite first jets.
Article: main_krylov, apB:lem:mu(c), actual finite oracle first-jet transfer.
Proof: Primitive coefficient smoothness derives the actual finite oracle-coordinate output regularity. Apply the real chain rule and identify each genuine finite-coordinate executor with its actual complete-history prefix. -/
theorem actual_gradient_firstJet_transfer (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N)
    (A B A' B' : ℝ → ℕ → E →L[ℝ] E) (dA dB : ℕ → E →L[ℝ] E)
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hA0' : A' 0=fun _ => Q) (hB0' : B' 0=fun _ => Q)
    (hA : ∀ i<N, HasDerivAt (fun t => A t i) (dA i) 0)
    (hB : ∀ i<N, HasDerivAt (fun t => B t i) (dB i) 0)
    (hA' : ∀ i<N, HasDerivAt (fun t => A' t i) (dA i) 0)
    (hB' : ∀ i<N, HasDerivAt (fun t => B' t i) (dB i) 0) :
    deriv (fun t => probedGradient m (A t) (B t) g N) 0=
      deriv (fun t => probedGradient m (A' t) (B' t) g N) 0 := by
  -- Derive the actual raw cycle regularity from primitive coefficients before transferring its real first derivative.
  have hf := finiteOracle_gradient_regular m hm Q hQ hpos g N hpre hsmooth
  have he := finiteOracle_firstJet_transfer Q N
    (fun p => probedGradient m (finiteOracleExtension Q p.1) (finiteOracleExtension Q p.2) g N)
    (hf.differentiableAt (by norm_num)) A B A' B' dA dB hA0 hB0 hA0' hB0' hA hB hA' hB'
  have hleft : (fun t => probedGradient m (finiteOracleExtension Q (fun i : Fin N => A t i.val))
      (finiteOracleExtension Q (fun i : Fin N => B t i.val)) g N)=fun t => probedGradient m (A t) (B t) g N := by
    funext t
    exact congrArg History.gradient (finiteOracleExtension_run m Q (A t) (B t) g N)
  have hright : (fun t => probedGradient m (finiteOracleExtension Q (fun i : Fin N => A' t i.val))
      (finiteOracleExtension Q (fun i : Fin N => B' t i.val)) g N)=fun t => probedGradient m (A' t) (B' t) g N := by
    funext t
    exact congrArg History.gradient (finiteOracleExtension_run m Q (A' t) (B' t) g N)
  rwa [hleft,hright] at he
end
end krylov.Envelope
