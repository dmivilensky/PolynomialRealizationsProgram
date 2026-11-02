import krylov.Functions.NativeRFCF
import krylov.Methods.WindowCoordinates

/-!
Article: main_krylov, prop:Fcycle(i), genuine value-model coordinates.
Use: reverse the actual chronological pairs and rescale the current searched
segment back to its true probed direction without changing the actual final
physical correction. The scalar value corrections are the observed ones;
no cubic identity or asymptotic model is an input to these exact identities.
Source: genuine latest-model indexing and the existing totalized inverse
coordinate-change theorems.
-/

namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Reversing genuine chronological pairs gives exactly the actual newest-first pair model.
Article: main_krylov, prop:Fcycle, exact indexing dictionary. -/
theorem latest_crossGram_reverse (s y : Fin n → E) :
    (krylov.Secant.latest (crossGram s y)).submatrix Fin.rev Fin.rev=
      pairModel (s ∘ Fin.rev) (y ∘ Fin.rev) := by
  ext i j
  rcases le_total i j with hij | hji
  · have hrev : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    simp only [submatrix_apply,krylov.Secant.latest,crossGram,pairModel,Function.comp_apply,
      min_eq_right hrev,max_eq_left hrev,min_eq_left hij,max_eq_right hij]
  · have hrev : i.rev ≤ j.rev := Fin.rev_le_rev.mpr hji
    simp only [submatrix_apply,krylov.Secant.latest,crossGram,pairModel,Function.comp_apply,
      min_eq_left hrev,max_eq_right hrev,min_eq_right hji,max_eq_left hji]

/-- An actual diagonal correction relabels by precisely the same chronological reversal.
Article: main_krylov, prop:Fcycle, scalar value observations. -/
theorem diagonal_reverse (d : Fin n → ℝ) :
    (Matrix.diagonal d).submatrix Fin.rev Fin.rev=Matrix.diagonal (d ∘ Fin.rev) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp only [submatrix_apply,diagonal_apply_eq,Function.comp_apply]
  · have hrev : i.rev≠j.rev := fun h=>hij (Fin.rev_injective h)
    simp only [submatrix_apply,diagonal_apply_ne _ hrev,diagonal_apply_ne _ hij]

/-- The actual observed value-corrected model has its precise chronological secant representation.
Article: main_krylov, equation (function-value-model). -/
theorem valueCorrectedModel_gradient (f : E → ℝ) (G : E → E)
    (a s : Fin n → E) (l : Fin n → ℝ) :
    valueCorrectedModel f (fun x=>innerSL ℝ (G x)) a s l=
      krylov.Secant.latest (crossGram s (fun i=>G (a i+s i)-G (a i)))-
        Matrix.diagonal (fun i=>12*l i*segmentValueDefect f (fun x=>innerSL ℝ (G x)) (a i) (s i)) := by
  unfold valueCorrectedModel
  congr 1
  ext i j
  simp only [krylov.Secant.latest,crossGram,_root_.sub_apply,innerSL_apply_apply,
    inner_sub_right]
  rw [real_inner_comm (s (min i j)) (G (a (max i j)+s (max i j))),
    real_inner_comm (s (min i j)) (G (a (max i j)))]

/-- The complete true value model is unchanged physically by chronological reversal.
Article: main_krylov, prop:Fcycle, observed final model solve. -/
theorem valueModelCorrection_reverse (s y : Fin n → E) (d : Fin n → ℝ) (g : E) :
    combine (s ∘ Fin.rev)
      (modelCoefficients (s ∘ Fin.rev)
        (pairModel (s ∘ Fin.rev) (y ∘ Fin.rev)+Matrix.diagonal (d ∘ Fin.rev)) g)=
      combine s (modelCoefficients s (krylov.Secant.latest (crossGram s y)+Matrix.diagonal d) g) := by
  have he : (krylov.Secant.latest (crossGram s y)+Matrix.diagonal d).submatrix Fin.rev Fin.rev=
      pairModel (s ∘ Fin.rev) (y ∘ Fin.rev)+Matrix.diagonal (d ∘ Fin.rev) := by
    change (krylov.Secant.latest (crossGram s y)).submatrix Fin.rev Fin.rev+
      (Matrix.diagonal d).submatrix Fin.rev Fin.rev=_
    rw [latest_crossGram_reverse,diagonal_reverse]
  rw [←he]
  exact modelCorrection_reindex (Fin.revPerm) s _ g

/-- Rescaling the actual basis transforms its genuine diagonal value change by the square column scales.
Article: main_krylov, prop:Fcycle, rescale the newest actual searched segment. -/
theorem rescaleModel_diagonal (d c : Fin n → ℝ) :
    rescaleModel (Matrix.diagonal d) c=Matrix.diagonal (fun i=>c i^2*d i) := by
  simp only [rescaleModel,diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/-- Every nonzero actual column rescaling preserves the complete changed-model physical correction.
Article: main_krylov, prop:Fcycle, exact final observed-model coordinate change.
Proof: derive the diagonal change in raw probed coordinates and apply the
existing exact inverse congruence, including its totalized singular cases. -/
theorem valueModelCorrection_rescale (s y : Fin n → E) (d c : Fin n → ℝ)
    (hc : ∀ i,c i≠0) (g : E) :
    combine (rescaleWindow s c)
      (modelCoefficients (rescaleWindow s c)
        (pairModel (rescaleWindow s c) (rescaleWindow y c)+Matrix.diagonal d) g)=
      combine s (modelCoefficients s
        (pairModel s y+Matrix.diagonal (fun i=>d i/c i^2)) g) := by
  have hunit : IsUnit (Matrix.diagonal c).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _=>hc i)
  have he : rescaleModel (pairModel s y+Matrix.diagonal (fun i=>d i/c i^2)) c=
      pairModel (rescaleWindow s c) (rescaleWindow y c)+Matrix.diagonal d := by
    rw [rescaleModel,Matrix.mul_add,Matrix.add_mul,←rescaleModel,←pairModel_rescale,
      ←rescaleModel,rescaleModel_diagonal]
    congr 1
    apply congrArg Matrix.diagonal
    funext i
    exact mul_div_cancel₀ (d i) (pow_ne_zero 2 (hc i))
  rw [←he]
  exact modelCorrection_rescale s _ c hunit g

end
end krylov.Functions
