import krylov.Envelope.ModelCorrectionFirstJet
set_option autoImplicit false
/-!
Article: main_krylov, thm:I and prop:launch, true native correction first jets.
Use: differentiate original projected native outputs with an exact reference
model and arbitrary real incoming launch gradient.
Source: the existing actual model normal equation, primitive smooth native
inverse calculus and the real zero-reference-error product rule.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Stability
open scoped BigOperators Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual projected native correction first derivative is its true
model-error-entry derivative times the original native reference coefficients.
Use: no derivative of a solved coefficient contributes when the real reference
model is exact, even with a nonzero evaluated launch gradient.
Article: main_krylov, thm:I and prop:launch.
Proof: real primitive finite solve calculus gives the true coefficient jets.
The native normal equation holds on its genuine open determinant domain;
its error entries vanish at the reference, so finite scalar product
differentiation freezes exactly the actual native reference coefficients. -/
theorem modelCorrection_projected_first_jet (s : ℝ → ι → E) (H : ℝ → Matrix ι ι ℝ)
    (B : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hs : ∀ i,ContDiffAt ℝ 1 (fun t => s t i) 0)
    (hH : ∀ i j,ContDiffAt ℝ 1 (fun t => H t i j) 0)
    (hB : ContDiffAt ℝ 1 B 0) (hg : ContDiffAt ℝ 1 g 0)
    (hdet : (H 0).det≠0) (hmodel : correctionCompression (s 0) (B 0)=H 0) (i : ι) :
    deriv (fun t => inner ℝ (s t i)
      (g t+B t (combine (s t) (modelCoefficients (s t) (H t) (g t))))) 0=
      ∑ j,deriv (fun t => (correctionCompression (s t) (B t)-H t) i j) 0*
        modelCoefficients (s 0) (H 0) (g 0) j := by
  let w := fun t => modelCoefficients (s t) (H t) (g t)
  let F := fun t => correctionCompression (s t) (B t)-H t
  have hw : ∀ j,ContDiffAt ℝ 1 (fun t => w t j) 0 := contDiff_modelCoefficients s H g 0 hs hH hg hdet
  have hF (j : ι) : ContDiffAt ℝ 1 (fun t => F t i j) 0 :=
    ((hs i).inner ℝ (hB.clm_apply (hs j))).sub (hH i j)
  have hF0 : F 0=0 := by dsimp only [F];rw [hmodel,sub_self]
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ),IsUnit (H t).det := by
    have hc : ContinuousAt (fun t => (H t).det) 0 :=
      continuous_id.matrix_det.continuousAt.comp
        (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => (hH i j).continuousAt)))
    exact (hc.eventually_ne hdet).mono (fun _ ht => isUnit_iff_ne_zero.mpr ht)
  have he : (fun t => inner ℝ (s t i) (g t+B t (combine (s t) (w t))))=ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ j,F t i j*w t j) := by
    filter_upwards [hunit] with t ht
    exact congrFun (modelCorrection_projected_coefficients (s t) (H t) ht (B t) (g t)) i
  have hd (j : ι) : HasDerivAt (fun t => F t i j*w t j)
      (deriv (fun t => F t i j) 0*w 0 j) 0 := by
    simpa only [hF0,Matrix.zero_apply,zero_mul,add_zero] using
      ((hF j).differentiableAt (by norm_num)).hasDerivAt.fun_mul
        ((hw j).differentiableAt (by norm_num)).hasDerivAt
  exact he.deriv_eq.trans (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)).deriv

end
end krylov.Envelope
