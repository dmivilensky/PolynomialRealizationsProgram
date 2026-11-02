import krylov.Correction.ModelError
import krylov.Methods.DirectionReindex
import krylov.LinearAlgebra.MatrixNormBounds
import Mathlib.Data.Fin.Rev

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii), original observed source coordinates.
Use: Transport actual uniform method conclusions and terminal model algebra
through the genuine finite source and chronological observation dictionary.
Source: proved true source-budget congruence, original active CG reference
geometry and exact finite latest-information model identities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Reversing both true newest-first model axes gives exactly the original chronological latest-information model.
Use: Apply the original uniform theory to the same actual method and observed source data.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The real reversal involution exchanges min and max, preserving each genuine observed pairing in the two triangles.
-/
theorem latest_crossGram_reverse_pairModel (s y : Fin p → E) :
    (pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm=latest (crossGram s y) := by
  ext i j
  change inner ℝ (s (Fin.rev (max (Fin.rev i) (Fin.rev j)))) (y (Fin.rev (min (Fin.rev i) (Fin.rev j))))=_
  by_cases hij : i≤j
  · have hji : Fin.rev j≤Fin.rev i := Fin.rev_le_rev.mpr hij
    simp only [max_eq_left hji,min_eq_right hji,Fin.rev_rev,latest,crossGram,min_eq_left hij,max_eq_right hij]
  · have hji : j≤ i := le_of_not_ge hij
    have hrev : Fin.rev i≤Fin.rev j := Fin.rev_le_rev.mpr hji
    simp only [max_eq_right hrev,min_eq_left hrev,Fin.rev_rev,latest,crossGram,min_eq_right hji,max_eq_left hji]

/-- The actual chronological latest-model difference is bounded by dimension times the genuine measured-image error on true unit columns.
Use: Derive real normalized model error in the uniform actual RFC response.
Article: main_krylov, thm:UCq.
Proof: Each original symmetric selected entry is a true unit-column pairing with the measured-image difference. Apply real Cauchy--Schwarz and the proved genuine spectral/Frobenius comparison.
-/
theorem latest_crossGram_difference_bound (s y z : Fin p → E) (hs : ∀ i, ‖s i‖=1)
    {η : ℝ} (hη : 0≤η) (hyz : ∀ i, ‖y i-z i‖≤η) :
    ‖latest (crossGram s y)-latest (crossGram s z)‖≤(p : ℝ)*η := by
  apply (spectral_le_hsNorm _).trans (hsNorm_le_dimension _ hη ?_)
  intro i j
  change |inner ℝ (s (min i j)) (y (max i j))-inner ℝ (s (min i j)) (z (max i j))|≤η
  rw [← inner_sub_right]
  have hi := norm_inner_le_norm (𝕜 := ℝ) (s (min i j)) (y (max i j)-z (max i j))
  rw [Real.norm_eq_abs,hs,one_mul] at hi
  exact hi.trans (hyz _)

/-- The actual measured-image error relative to its own linear operator keeps its true relative bound under genuine individual column-length normalization.
Use: Derive real normalized model error in the uniform actual RFC response.
Article: main_krylov, thm:UCq.
Proof: The actual linear operator commutes with the real reciprocal column scale. Bound the genuine scaled error and cancel its own nonzero original column norm.
-/
theorem unitWindow_image_error (s y : Fin p → E) (A : Fin p → E →L[ℝ] E)
    (hs : ∀ i, s i≠0) {η : ℝ} (hy : ∀ i, ‖y i-A i (s i)‖≤η*‖s i‖) (i : Fin p) :
    ‖rescaleWindow y (fun j => ‖s j‖⁻¹) i-A i (unitWindow s i)‖≤η := by
  change ‖‖s i‖⁻¹ • y i-A i (‖s i‖⁻¹ • s i)‖≤η
  rw [map_smul,← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (hy i) (inv_nonneg.mpr (norm_nonneg _))).trans_eq
    (by rw [mul_left_comm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hs i)),mul_one])


/-- The genuine chronological latest-information model has dimension-times-relative-observation spectral distance from its actual unit-column Gram.
Use: Apply the original uniform theory to the same actual method and observed source data.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: Each actual selected observation differs from its own true unit column by the given pair error. Cauchy--Schwarz bounds the genuine symmetric entry difference; the proved spectral/Frobenius comparison supplies the dimension factor.
-/
theorem latest_crossGram_gram_distance (s y : Fin p → E) (hs : ∀ i, ‖s i‖=1)
    {η : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η) :
    ‖latest (crossGram s y)-crossGram s s‖≤(p : ℝ)*η := by
  simpa only [latest_eq_of_isSymm (Matrix.isHermitian_iff_isSymm.mp (crossGram_isHermitian s))] using
    latest_crossGram_difference_bound s y s hs hη hy

end
end krylov.Correction
