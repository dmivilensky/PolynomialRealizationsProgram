import bezout.History.Execution
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: bezout, Theorems 3.1 and 4.1, temporal energy estimates.
Use: deterministic physical responses and the dimension-uniform relative
remainder are controlled by the same finite Cauchy--Schwarz inequality.
Proof: the real finite-sum inequality, followed by the triangle inequality.
-/

namespace bezout.Analysis
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Euclidean energy of a real temporal profile. -/
def energyNorm (a : ι → ℝ) : ℝ := Real.sqrt (∑ i, a i ^ 2)

/-- Temporal energy is always nonnegative. -/
theorem energyNorm_nonneg (a : ι → ℝ) : 0 ≤ energyNorm a := Real.sqrt_nonneg _

/-- Squaring temporal energy recovers its finite sum. -/
@[simp] theorem energyNorm_sq (a : ι → ℝ) : energyNorm a ^ 2 = ∑ i, a i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Finite real Cauchy--Schwarz with the article's temporal energy norm. -/
theorem sum_mul_le_energyNorm (a b : ι → ℝ) :
    ∑ i, a i * b i ≤ energyNorm a * energyNorm b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) a b
  have hn := mul_nonneg (energyNorm_nonneg a) (energyNorm_nonneg b)
  have hs : (energyNorm a * energyNorm b) ^ 2 =
      (∑ i, a i ^ 2) * ∑ i, b i ^ 2 := by rw [mul_pow, energyNorm_sq, energyNorm_sq]
  nlinarith [sq_nonneg ((∑ i, a i * b i) - energyNorm a * energyNorm b)]

/-- A squared energy budget bounds the corresponding temporal norm. -/
theorem energyNorm_le {a : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (ha : ∑ i, a i ^ 2 ≤ t ^ 2) : energyNorm a ≤ t := by
  apply (sq_le_sq₀ (energyNorm_nonneg a) ht).mp
  simpa using ha

/-- Cauchy--Schwarz with a prescribed nonnegative energy budget. -/
theorem sum_mul_le_of_energy {a b : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hb : ∑ i, b i ^ 2 ≤ t ^ 2) :
    ∑ i, a i * b i ≤ energyNorm a * t :=
  (sum_mul_le_energyNorm a b).trans
    (mul_le_mul_of_nonneg_left (energyNorm_le ht hb) (energyNorm_nonneg a))

/-- Each coordinate of a unit temporal budget is at most one in absolute value. -/
theorem abs_le_one_of_energy {a : ι → ℝ} (ha : ∑ i, a i ^ 2 ≤ 1) (i : ι) :
    |a i| ≤ 1 := by
  have hi : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one _).mp (hi.trans ha)

/-- The norm of a finite vector response is bounded by scalar temporal energy. -/
theorem norm_sum_le_energy {E : Type*} [NormedAddCommGroup E]
    (v : ι → E) (a : ι → ℝ) (ha : ∀ i, ‖v i‖ ≤ a i) :
    ‖∑ i, v i‖ ≤ ∑ i, a i :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ha i)

end
end bezout.Analysis
