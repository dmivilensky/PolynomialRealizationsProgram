import krylov.OneGradient.CompletionCG
import krylov.OneGradient.FibreMinimax
set_option autoImplicit false
/-!
Article: main_krylov, s5:info, original information fibres and scenarios.
Use: expose the already proved physical restriction, prior pivot class,
reciprocal length ratio and genuine unobserved-output metric as named source data.
Source: true physical Krylov action and the complete positive Lanczos-fibre
characterization; the scenario error is the existing real executor quantity. -/

/-!
Article: krylov, Definition C.5 [s5:info].

The information is the actual positive operator restriction on the old Krylov flag. Prior
membership is imposed on physical completions; the output budget is the own-base operator norm.
The coordinate pivot is supplied only after identifying the whole physical information fibre.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant
variable {n m : ℕ}

/-- Positive physical matrices sharing the original Krylov information,
with the same fixed observed initial gradient.
Use: the class is the actual operator restriction, before selecting coordinates.
Article: main_krylov, s5:info. -/
def krylovInformationFibre (A : Matrix (Fin m) (Fin m) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {C | C.PosDef ∧ ∀ v∈CG.krylovSpace (cgOperator A) g N,cgOperator C v=cgOperator A v}

/-- The admissible physical last-pivot parameters for one original prior.
Use: the prior is imposed on the real completion matrix, not scalar surrogate data.
Article: main_krylov, s5:info. -/
def fibreAdmissiblePivots
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) : Set ℝ :=
  {b | lanczosCompletion A hA g hg hc b∈prior}

/-- The source information ratio in its actual physical affine-pivot coordinates.
Use: the interval endpoint exact lengths are reciprocal pivot distances.
Article: main_krylov, s5:info. -/
def fibreStepRatio (sigma lo hi : ℝ) : ℝ := (hi-sigma)/(lo-sigma)

/-- The actual unobserved-output relative matrix budget of a source scenario.
Use: the output matrix is absent from every actual policy observation.
Article: main_krylov, s5:info. -/
def fibreOutputBudget
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  relativeBudget (lanczosCompletion A hA g hg hc b) (B-lanczosCompletion A hA g hg hc b)

/-- The named original information fibre is exactly the complete positive
physical last-Lanczos family, with no missing symmetric completions.
Use: the source information definition connects to every existing minimax result.
Article: main_krylov, s5:info and s5:fibre(a).
Proof: the already proved whole physical fibre characterization gives both
inclusions, including its independently derived strict positive pivot domain. -/
theorem krylov_information_fibre_dictionary
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    krylovInformationFibre A g n=(lanczosCompletion A hA g hg hc) ''
      Set.Ioi (lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹) := by
  ext C
  rw [krylovInformationFibre,Set.mem_ofPred_eq,physical_information_fibre A hA g hg hc C]
  exact ⟨fun ⟨b,hb,he⟩ => ⟨b,hb,he.symm⟩,fun ⟨b,hb,he⟩ => ⟨b,hb,he.symm⟩⟩

/-- Every original prior fibre is exactly its admissible positive pivot image.
Use: arbitrary prior classes retain their full genuine physical information fibre.
Article: main_krylov, s5:info.
Proof: the complete positive physical fibre dictionary and the literal prior
membership of the same actual completion identify both intersections. -/
theorem prior_information_fibre_dictionary
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) :
    krylovInformationFibre A g n∩prior=(lanczosCompletion A hA g hg hc) ''
      (Set.Ioi (lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹)∩
        fibreAdmissiblePivots A hA g hg hc prior) := by
  rw [krylov_information_fibre_dictionary A hA g hg hc]
  ext C
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hp⟩
    exact ⟨b,⟨hb,hp⟩,rfl⟩
  · rintro ⟨b,⟨hb,hp⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,hp⟩

/-- The source endpoint ratio is literally the ratio of its two positive
reciprocal exact lengths, including a collapsed interval.
Use: interval minimax formulas use the same named physical information ratio.
Article: main_krylov, s5:info.
Proof: both actual pivot distances are nonzero; cancel their real reciprocals. -/
theorem fibre_step_ratio_reciprocals (sigma lo hi : ℝ) (hlo : sigma<lo) (horder : lo≤hi) :
    (1/(lo-sigma))/(1/(hi-sigma))=fibreStepRatio sigma lo hi := by
  have hl : lo-sigma≠0 := (sub_pos.mpr hlo).ne'
  have hh : hi-sigma≠0 := (sub_pos.mpr (hlo.trans_le horder)).ne'
  simp only [fibreStepRatio]
  field_simp

end
end krylov.OneGradient
