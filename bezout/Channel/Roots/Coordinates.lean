import bezout.Channel.Roots.Variance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: bezout, Proposition D.1, finite channel law in an actual Hilbert space.
Use: the spectral-coordinate product and variance are the terminal and Euclidean
squared error of the same physical oracle history, in every finite dimension.
Proof: arbitrary causal oracle executions commute with a linear coordinate
isomorphism; apply the finite-mode product and the Euclidean norm identity.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

section Transport
variable {N : ℕ} {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Conjugate every actual time-dependent oracle by an exact linear coordinate change. -/
def conjugateOracle (e : E ≃ₗ[ℝ] F) (oracle : Fin N → E → E) : Fin N → F → F :=
  fun s y => e (oracle s (e.symm y))

/-- The entire actual causal output commutes with an exact change of coordinates. -/
theorem oracleOutput_conjugate (h : bezout.History N) (e : E ≃ₗ[ℝ] F)
    (initial : E) (oracle : Fin N → E → E) :
    h.oracleOutput (e initial) (conjugateOracle e oracle)=e (h.oracleOutput initial oracle) := by
  have ha : (fun s => e (h.oracleAnswers initial oracle s))=
      h.oracleAnswers (e initial) (conjugateOracle e oracle) := by
    apply h.oracleAnswers_unique
    intro s
    rw [h.oracleAnswers_eq]
    unfold conjugateOracle
    have hq : e initial-∑ j,h.a s j • e (h.oracleAnswers initial oracle j)=
        e (h.oracleQuery initial oracle s) := by
      simp only [bezout.History.oracleQuery,map_sub,map_sum,map_smul]
    rw [hq,e.symm_apply_apply]
  unfold bezout.History.oracleOutput
  rw [← ha]
  simp only [map_sub,map_sum,map_smul]

end Transport

/-- The literal commuting-channel oracle acting on the finite Euclidean Hilbert space. -/
def euclideanOracle {ι : Type*} {N : ℕ} (eig : ι → ℝ) (δ : ℝ) (ξ : Fin N → ℝ) :
    Fin N → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
  conjugateOracle (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm (modeOracle eig δ ξ)

/-- Actual Euclidean terminal coordinates are the exact finite random mode products. -/
theorem euclidean_mode_product {ι : Type*} {N : ℕ} (α : Fin N → ℝ) (eig : ι → ℝ)
    (δ : ℝ) (ξ : Fin N → ℝ) (initial : ι → ℝ) :
    (history α).oracleOutput (WithLp.toLp 2 initial) (euclideanOracle eig δ ξ)=
      WithLp.toLp 2 (fun j => finiteMultiplier α (eig j) δ ξ*initial j) := by
  have h := oracleOutput_conjugate (history α)
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm initial (modeOracle eig δ ξ)
  rw [history_mode_product] at h
  exact h

/-- The full Euclidean finite-noise variance has exactly the product formula in D.1. -/
theorem euclidean_mode_variance {ι : Type*} [Fintype ι] {N : ℕ} (α : Fin N → ℝ)
    (eig : ι → ℝ) (initial : ι → ℝ) (δ : ℝ) :
    (∫ ω,‖(history α).oracleOutput (WithLp.toLp 2 initial)
      (euclideanOracle eig δ (fun s => Probability.SignProducts.sign s ω))-
      WithLp.toLp 2 (fun j => (terminal α).eval (eig j)*initial j)‖^2 ∂Probability.Signs.law N)=
      ∑ j,initial j^2*((∏ s,((1-α s*eig j)^2+δ^2*α s^2))-(terminal α).eval (eig j)^2) := by
  have h := history_mode_variance α eig initial δ
  simp only [history_mode_product] at h
  simp only [euclidean_mode_product,EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,
    PiLp.sub_apply]
  exact h

end
end bezout.Channel.Roots
