import krylov.XR.ModelStep
import krylov.Secant.Model

/-!
Article: main_krylov, lem:anchor.
Use: prove invariance for the actual chronological latest-information
model and observed secant solve. The full displacement changes by the
anchor displacement; the physical virtual point and final trial point
are exactly invariant. Source: the newest-column identity and uniqueness
of the finite observed solve.
-/

/-!
Article: krylov, Lemma F.7 [lem:anchor].

Virtual point/gradient, direction, length and physical trial point are unchanged by the last-
pair anchor shift; the displacement itself changes by minus the last step.
The virtual solve requires an invertible latest model and the trial-length step also uses
invertible conjugacy.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Methods krylov.Secant
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- The latest-information model retains the actual newest observed
column, including every incompatible older secant pair. Article: lem:anchor. -/
theorem latest_newest_column (s y : Fin (p+1) → E) :
    latest (crossGram s y)*ᵥ Pi.single (Fin.last p) 1=
      coordinates s (y (Fin.last p)) := by
  rw [mulVec_single]
  simp only [MulOpposite.op_one,one_smul]
  ext i
  change latest (crossGram s y) i (Fin.last p)=inner ℝ (s i) (y (Fin.last p))
  simp only [latest,crossGram,min_eq_left (Fin.le_last i),max_eq_right (Fin.le_last i)]

/-- Moving the anchor by the newest pair subtracts precisely its unit
coordinate from the actual model correction. Article: lem:anchor. -/
theorem modelCoefficients_anchor (s y : Fin (p+1) → E) (g : E)
    (hT : IsUnit (latest (crossGram s y)).det) :
    modelCoefficients s (latest (crossGram s y)) (g+y (Fin.last p))=
      modelCoefficients s (latest (crossGram s y)) g-Pi.single (Fin.last p) 1 := by
  have hc : coordinates s (g+y (Fin.last p))=
      coordinates s g+coordinates s (y (Fin.last p)) := by
    ext i
    exact inner_add_right _ _ _
  have hi : (latest (crossGram s y))⁻¹*ᵥ coordinates s (y (Fin.last p))=
      Pi.single (Fin.last p) 1 := by
    rw [←latest_newest_column s y,mulVec_mulVec,nonsing_inv_mul _ hT,one_mulVec]
  rw [modelCoefficients,hc,mulVec_add,hi,modelCoefficients]
  abel

/-- Synthesizing a shifted coefficient vector subtracts its literal
stored step. Article: main_krylov, lem:anchor. -/
theorem combine_sub_single (s : Fin (p+1) → E) (w : Fin (p+1) → ℝ) (i : Fin (p+1)) :
    combine s (w-Pi.single i 1)=combine s w-s i := by
  simp [combine,sub_smul,Finset.sum_sub_distrib]

/-- The actual model virtual point is independent of the chosen newest
anchor. Article: main_krylov, lem:anchor. -/
theorem modelVirtualPoint_anchor (s y : Fin (p+1) → E) (x g : E)
    (hT : IsUnit (latest (crossGram s y)).det) :
    x+s (Fin.last p)+modelVirtualCorrection s (latest (crossGram s y)) (g+y (Fin.last p))=
      x+modelVirtualCorrection s (latest (crossGram s y)) g := by
  rw [modelVirtualCorrection,modelCoefficients_anchor s y g hT,combine_sub_single,
    modelVirtualCorrection]
  abel

/-- Extrapolated gradients computed from the original observed data
are exactly anchor invariant. Article: main_krylov, lem:anchor. -/
theorem modelVirtualGradient_anchor (s y : Fin (p+1) → E) (g : E)
    (hT : IsUnit (latest (crossGram s y)).det) :
    modelVirtualGradient s y (latest (crossGram s y)) (g+y (Fin.last p))=
      modelVirtualGradient s y (latest (crossGram s y)) g := by
  rw [modelVirtualGradient,modelCoefficients_anchor s y g hT,combine_sub_single,
    modelVirtualGradient]
  abel

/-- The true observed conjugacy direction is exactly anchor invariant.
Article: main_krylov, lem:anchor. -/
theorem modelDirection_anchor (s y : Fin (p+1) → E) (g : E)
    (hT : IsUnit (latest (crossGram s y)).det) :
    modelDirection s y (latest (crossGram s y)) (g+y (Fin.last p))=
      modelDirection s y (latest (crossGram s y)) g := by
  simp only [modelDirection,modelVirtualGradient_anchor s y g hT]

/-- The actual scalar trial length is invariant because the newest
image is conjugate to the computed direction. Article: lem:anchor. -/
theorem modelTrialLength_anchor (s y : Fin (p+1) → E) (g : E) (c : ℝ)
    (hT : IsUnit (latest (crossGram s y)).det) (hY : IsUnit (crossGram y s).det) :
    modelTrialLength s y (latest (crossGram s y)) (g+y (Fin.last p)) c=
      modelTrialLength s y (latest (crossGram s y)) g c := by
  have hc := congrFun (modelDirection_conjugate s y (latest (crossGram s y)) hY g) (Fin.last p)
  change inner ℝ (y (Fin.last p)) (modelDirection s y (latest (crossGram s y)) g)=0 at hc
  simp only [modelTrialLength,modelDirection_anchor s y g hT,inner_add_left,hc,add_zero]

/-- The full physical displacement transforms by subtracting the anchor
shift. Consequently the actual trial point is unchanged. Article: lem:anchor. -/
theorem modelTrialPoint_anchor (s y : Fin (p+1) → E) (x g : E) (c : ℝ)
    (hT : IsUnit (latest (crossGram s y)).det) (hY : IsUnit (crossGram y s).det) :
    x+s (Fin.last p)+modelTrialStep s y (latest (crossGram s y)) (g+y (Fin.last p)) c=
      x+modelTrialStep s y (latest (crossGram s y)) g c := by
  simp only [modelTrialStep,modelTrialLength_anchor s y g c hT hY,modelDirection_anchor s y g hT]
  rw [←add_assoc,modelVirtualPoint_anchor s y x g hT,add_assoc]

end
end krylov.XR
