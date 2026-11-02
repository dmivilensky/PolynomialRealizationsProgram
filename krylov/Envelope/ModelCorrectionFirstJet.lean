import krylov.Methods.NormalizedCorrection
import krylov.Stability.ContDiffSolve
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(a), genuine C-one latest-model residual cancellation.
Use: prove real final Galerkin projected-residual first derivatives
vanish from actual observed model data under the source smoothness
assumptions, without an extra analytic-policy premise.
Source: the proved exact physical model-correction normal equations
and the standard true product derivative rule at two vanishing factors.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Stability Matrix Filter Topology
open scoped BigOperators Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual physical model correction has projected residual exactly equal to the true model error times its real solved coefficient vector.
Use: The actual physical model correction has projected residual exactly equal to the true model error times its real solved coefficient vector.
Article: main_krylov, apB:lem:mu(a), genuine C-one latest-model residual cancellation.
Proof: Rewrite the proved genuine model normal equation using the actual inverse-model coefficient definition. -/
theorem modelCorrection_projected_coefficients (s : ι → E) (H : Matrix ι ι ℝ)
    (hH : IsUnit H.det) (B : E →L[ℝ] E) (g : E) :
    coordinates s (g+B (combine s (modelCoefficients s H g)))=
      (correctionCompression s B-H) *ᵥ modelCoefficients s H g := by
  rw [modelCorrection_projected s H hH B g]
  simp only [modelCoefficients,Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.neg_mulVec]

/-- Every actual latest-model corrected projection has zero true first derivative when its genuine reference model is exact and its real incoming projected gradient vanishes, under C-one observed data.
Use: Every actual latest-model corrected projection has zero true first derivative when its genuine reference model is exact and its real incoming projected gradient vanishes, under C-one observed data.
Article: main_krylov, apB:lem:mu(a), genuine C-one latest-model residual cancellation.
Proof: Primitive true inverse-model coefficients are C-one on their actual determinant domain. The genuine model error and real correction coefficients both vanish at the reference. Their actual finite product sum therefore has zero true derivative; the genuine model normal equation identifies the real corrected projection on its actual nonsingular neighborhood. -/
theorem modelCorrection_projected_deriv_zero (s : ℝ → ι → E) (H : ℝ → Matrix ι ι ℝ)
    (B : ℝ → E →L[ℝ] E) (g : ℝ → E)
    (hs : ∀ i, ContDiffAt ℝ 1 (fun t => s t i) 0)
    (hH : ∀ i j, ContDiffAt ℝ 1 (fun t => H t i j) 0)
    (hB : ContDiffAt ℝ 1 B 0) (hg : ContDiffAt ℝ 1 g 0)
    (hdet : (H 0).det≠0) (hmodel : correctionCompression (s 0) (B 0)=H 0)
    (hρ : coordinates (s 0) (g 0)=0) (i : ι) :
    deriv (fun t => inner ℝ (s t i) (g t+B t (combine (s t) (modelCoefficients (s t) (H t) (g t))))) 0=0 := by
  -- The actual model-error entries and true solved coefficient vector both vanish at the genuine quadratic reference.
  let w := fun t => modelCoefficients (s t) (H t) (g t)
  let F := fun t => correctionCompression (s t) (B t)-H t
  have hw : ∀ j, ContDiffAt ℝ 1 (fun t => w t j) 0 := contDiff_modelCoefficients s H g 0 hs hH hg hdet
  have hF (j : ι) : ContDiffAt ℝ 1 (fun t => F t i j) 0 :=
    ((hs i).inner ℝ (hB.clm_apply (hs j))).sub (hH i j)
  have hF0 : F 0=0 := by dsimp only [F];rw [hmodel,sub_self]
  have hw0 : w 0=0 := modelCoefficients_zero (s 0) (H 0) (g 0) hρ
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (H t).det := by
    have hc : ContinuousAt (fun t => (H t).det) 0 :=
      continuous_id.matrix_det.continuousAt.comp (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => (hH i j).continuousAt)))
    exact (hc.eventually_ne hdet).mono (fun _ ht => isUnit_iff_ne_zero.mpr ht)
  -- The genuine inverse domain holds on an actual neighborhood, so the exact real normal equation transfers the true product derivative.
  have he : (fun t => inner ℝ (s t i) (g t+B t (combine (s t) (w t))))=ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ j, F t i j*w t j) := by
    filter_upwards [hunit] with t ht
    exact congrFun (modelCorrection_projected_coefficients (s t) (H t) ht (B t) (g t)) i
  have hd (j : ι) : HasDerivAt (fun t => F t i j*w t j) 0 0 := by
    have hf := ((hF j).differentiableAt (by norm_num)).hasDerivAt.mul ((hw j).differentiableAt (by norm_num)).hasDerivAt
    convert! hf using 1
    simp [hF0,hw0]
  have hsum : HasDerivAt (fun t => ∑ j, F t i j*w t j) 0 0 := by
    convert! HasDerivAt.sum (fun j (_ : j∈Finset.univ) => hd j) using 1
    · funext t
      exact (Finset.sum_apply t Finset.univ (fun j t => F t i j*w t j)).symm
    · simp only [Finset.sum_const_zero]
  exact he.deriv_eq.trans hsum.deriv
end
end krylov.Envelope
