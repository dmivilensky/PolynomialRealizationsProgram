import krylov.Methods.ProjectedModel
import krylov.Secant.Model
import Mathlib.Tactic.NoncommRing
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual observed pair coordinates.
Use: compare finite secant solves on the same actual data after a genuine
common change of their recorded vector families.
Source: finite real inner-product linearity and nonsingular matrix algebra.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Apply a genuine common column change to an actual finite vector family.
Use: recorded steps and replay directions are compared on the same history.
Article: main_krylov, thm:local(a), actual observed column change. -/
def rightChange (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) : E :=
  combine s (fun i => T i j)

/-- Physical synthesis commutes with a true observed column change.
Use: a changed finite solve is identified before any asymptotic estimate.
Article: main_krylov, thm:local(a), finite physical synthesis.
Proof: distribute the finite scalar sums and interchange the two indices. -/
theorem combine_rightChange (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (w : Fin p → ℝ) :
    combine (rightChange s T) w=combine s (T *ᵥ w) := by
  simp only [combine,rightChange,Finset.smul_sum,smul_smul,Matrix.mulVec,dotProduct,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- Actual observed coordinates transform by the transpose change.
Use: both genuine virtual and conjugacy right-hand sides are transported.
Article: main_krylov, thm:local(a), real observed coordinate change.
Proof: expand the finite physical sum and real inner-product linearity. -/
theorem coordinates_rightChange (s : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) (v : E) :
    coordinates (rightChange s T) v=Tᵀ *ᵥ coordinates s v := by
  ext i
  simp only [coordinates,rightChange,combine,sum_inner,real_inner_smul_left,
    Matrix.mulVec,dotProduct,Matrix.transpose_apply]

/-- Common actual pair changes give the true Gram congruence.
Use: retain the nonsymmetric observed pairing before selecting latest data.
Article: main_krylov, thm:local(a), genuine pairing congruence.
Proof: the observed right-hand side and physical column synthesis each
transform by their proved finite matrix action. -/
theorem crossGram_rightChange (s y : Fin p → E) (T : Matrix (Fin p) (Fin p) ℝ) :
    crossGram (rightChange y T) (rightChange s T)=Tᵀ*crossGram y s*T := by
  ext i j
  have h := congrFun (coordinates_rightChange y T (rightChange s T j)) i
  rw [show coordinates y (rightChange s T j)=crossGram y s *ᵥ (fun l => T l j) from
    coordinates_combine y s _ ,Matrix.mulVec_mulVec] at h
  exact h

/-- The actual newest-first pair model is the latest selector of its
true observed cross Gram matrix, including incompatible secant pairs.
Use: no off-quadratic symmetry of observed pairings is assumed.
Article: main_krylov, thm:local(a), actual latest-model dictionary.
Proof: the two definitions select the same entries, with real symmetry. -/
theorem pairModel_eq_latest (s y : Fin p → E) :
    pairModel s y=krylov.Secant.latest (crossGram y s) := by
  ext i j
  exact real_inner_comm _ _

/-- A genuine invertible common column change cancels exactly in every
inverse pairing solve, even if the pairing matrix itself is singular.
Use: basis invariance precedes the native nonsingularity-domain analysis.
Article: main_krylov, thm:local(a), exact inverse pairing congruence.
Proof: reverse the actual inverse product and cancel the true change and
its transpose on their nonsingular domains. -/
theorem inverse_pairing_change (T C : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) :
    T*(Tᵀ*C*T)⁻¹*Tᵀ=C⁻¹ := by
  have ht : IsUnit Tᵀ.det := by simpa only [Matrix.det_transpose] using hT
  simp only [Matrix.mul_inv_rev]
  calc
    _=(T*T⁻¹)*C⁻¹*(Tᵀ⁻¹*Tᵀ) := by noncomm_ring
    _=C⁻¹ := by rw [Matrix.mul_nonsing_inv _ hT,Matrix.nonsing_inv_mul _ ht,Matrix.one_mul,Matrix.mul_one]

/-- The genuine FC direction is exactly invariant under an invertible
common observed pair change, with no quadratic-data premise.
Use: compare real S and D fields on the same actual native history.
Article: main_krylov, thm:local(a), actual conjugacy solve invariance.
Proof: transport the genuine right-hand side and physical synthesis;
the exact inverse pairing congruence cancels their common basis change. -/
theorem conjugacyDirection_rightChange (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (hT : IsUnit T.det) (v : E) :
    conjugacyDirection (rightChange s T) (rightChange y T) v=conjugacyDirection s y v := by
  simp only [conjugacyDirection,conjugacyCoefficients,crossGram_rightChange,
    coordinates_rightChange,combine_rightChange,Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc,inverse_pairing_change T _ hT]

end
end krylov.Methods
