import krylov.Envelope.ModelCorrectionFirstJet

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine target-relative model first jets.
Use: derive actual C-r target-corrected outputs and true zero explored first derivatives when their genuine reference gradient equals the fixed target.
Source: proved inverse-model coefficient calculus and the actual C-one model normal-equation cancellation, using only real primitive input regularity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Stability Matrix
open scoped BigOperators Matrix.Norms.Elementwise
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual target-relative model output is the true incoming gradient plus its genuine one-query model correction.
Use: The actual target-relative model output is the true incoming gradient plus its genuine one-query model correction.
Article: main_krylov, apB:prop:consist, genuine target-relative model first jets.
Proof: Solve the real observed model with the actual incoming gradient minus the fixed prior target. -/
def targetModelOutput (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E) (g target : E) : E :=
  g+B (combine s (modelCoefficients s H (g-target)))

/-- The genuine target-relative model output is C-r on its actual nonsingular primitive model domain.
Use: The genuine target-relative model output is C-r on its actual nonsingular primitive model domain.
Article: main_krylov, apB:prop:consist, genuine target-relative model first jets.
Proof: Compose the proved real inverse-model coefficient calculus with genuine synthesis and the actual correction operator. -/
theorem targetModelOutput_contDiffAt (s : X → ι → E) (H : X → Matrix ι ι ℝ)
    (B : X → E →L[ℝ] E) (g : X → E) (target : E) (x : X) (r : WithTop ℕ∞)
    (hs : ∀ i,ContDiffAt ℝ r (fun p => s p i) x)
    (hH : ∀ i j,ContDiffAt ℝ r (fun p => H p i j) x)
    (hB : ContDiffAt ℝ r B x) (hg : ContDiffAt ℝ r g x) (hdet : (H x).det≠0) :
    ContDiffAt ℝ r (fun p => targetModelOutput (s p) (H p) (B p) (g p) target) x := by
  have hw := contDiff_modelCoefficients s H (fun p => g p-target) x hs hH (hg.sub contDiffAt_const) hdet
  have hu : ContDiffAt ℝ r (fun p => combine (s p) (modelCoefficients (s p) (H p) (g p-target))) x :=
    ContDiffAt.sum (fun i _ => (hw i).smul (hs i))
  exact hg.add (hB.clm_apply hu)

/-- At the genuine target gradient the actual model query is zero and the real output equals that target.
Use: At the genuine target gradient the actual model query is zero and the real output equals that target.
Article: main_krylov, apB:prop:consist, genuine target-relative model first jets.
Proof: The true zero right-hand side has actual zero inverse-model coefficients. -/
theorem targetModelOutput_at_target (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E) (target : E) :
    targetModelOutput s H B target target=target := by
  have hz : coordinates s (0 : E)=0 := by ext i;exact inner_zero_right _
  simp only [targetModelOutput,sub_self,modelCoefficients_zero s H 0 hz,combine,Pi.zero_apply,
    zero_smul,Finset.sum_const_zero,map_zero,add_zero]

/-- If the real reference gradient equals the fixed target and the actual model is exact, every true model-basis coordinate of the genuine output derivative vanishes.
Use: If the real reference gradient equals the fixed target and the actual model is exact, every true model-basis coordinate of the genuine output derivative vanishes.
Article: main_krylov, apB:prop:consist, genuine target-relative model first jets.
Proof: Apply actual C-one model cancellation to the true gradient difference, whose reference value is zero; genuine product differentiation then removes all moving-basis terms. -/
theorem targetModelOutput_projected_deriv_zero (s : ℝ → ι → E) (H : ℝ → Matrix ι ι ℝ)
    (B : ℝ → E →L[ℝ] E) (g : ℝ → E) (target : E)
    (hs : ∀ i,ContDiffAt ℝ 1 (fun t => s t i) 0)
    (hH : ∀ i j,ContDiffAt ℝ 1 (fun t => H t i j) 0)
    (hB : ContDiffAt ℝ 1 B 0) (hg : ContDiffAt ℝ 1 g 0)
    (hdet : (H 0).det≠0) (hmodel : correctionCompression (s 0) (B 0)=H 0) (hgt : g 0=target) (i : ι) :
    inner ℝ (s 0 i) (deriv (fun t => targetModelOutput (s t) (H t) (B t) (g t) target) 0)=0 := by
  -- The actual corrected gradient difference vanishes at the genuine reference target.
  let G := fun t => targetModelOutput (s t) (H t) (B t) (g t) target
  let F := fun t => G t-target
  have hG : ContDiffAt ℝ 1 G 0 := targetModelOutput_contDiffAt s H B g target 0 1 hs hH hB hg hdet
  have hF : ContDiffAt ℝ 1 F 0 := hG.sub contDiffAt_const
  have hF0 : F 0=0 := by
    dsimp only [F,G]
    rw [hgt,targetModelOutput_at_target,sub_self]
  have hρ : coordinates (s 0) (g 0-target)=0 := by
    rw [hgt,sub_self]
    ext j
    exact inner_zero_right _
  -- The true model normal equation kills the derivative of every actual moving projected gradient difference.
  have hp := modelCorrection_projected_deriv_zero s H B (fun t => g t-target)
    hs hH hB (hg.sub contDiffAt_const) hdet hmodel hρ i
  have heq : (fun t => inner ℝ (s t i) (g t-target+B t (combine (s t) (modelCoefficients (s t) (H t) (g t-target)))))=
      fun t => inner ℝ (s t i) (F t) := by
    funext t
    congr 1
    dsimp only [F,G,targetModelOutput]
    abel
  rw [heq] at hp
  -- Since the genuine corrected difference is zero at the reference, product differentiation leaves only the actual output derivative.
  have hd := ((hs i).differentiableAt (by norm_num)).hasDerivAt.inner ℝ
    (hF.differentiableAt (by norm_num)).hasDerivAt
  change HasDerivAt (fun t => inner ℝ (s t i) (F t))
    (inner ℝ (s 0 i) (deriv F 0)+inner ℝ (deriv (fun t => s t i) 0) (F 0)) 0 at hd
  rw [hd.deriv,hF0,inner_zero_right,add_zero] at hp
  change inner ℝ (s 0 i) (deriv (fun t => G t-target) 0)=0 at hp
  rw [deriv_sub_const] at hp
  exact hp
end
end krylov.Envelope
