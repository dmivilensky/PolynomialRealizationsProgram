import krylov.Tensor.FlatFlagDictionary
import krylov.Functions.HarmonicCubic

/-!
Article: main_krylov, apG:flat, the genuine lower-bound cubic.
Use: construct the printed 3 sqrt(3) x y² tensor, certify its exact original
diagonal budget, and evaluate its true response slice.
Source: an elementary sharp polynomial inequality on the unit disk.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Functions
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance flatWitnessCurriedNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ)

/-- The actual continuous form of the printed flat-profile witness.
Article: main_krylov, apG:flat. -/
def flatWitnessForm (φ ψ : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  Real.sqrt 3 • (coordinateTriple φ ψ ψ + coordinateTriple ψ φ ψ + coordinateTriple ψ ψ φ)

/-- Exact evaluation in the genuine two linear coordinates.
Article: main_krylov, apG:flat. -/
theorem flatWitnessForm_apply (φ ψ : E →L[ℝ] ℝ) (x y z : E) :
    flatWitnessForm φ ψ x y z = Real.sqrt 3 *
      (φ x * (ψ y * ψ z) + ψ x * (φ y * ψ z) + ψ x * (ψ y * φ z)) := rfl

/-- The genuine symmetric trilinear flat-profile witness.
Article: main_krylov, apG:flat. -/
def flatWitnessCubic (φ ψ : E →L[ℝ] ℝ) : SymmetricCubic E where
  form := flatWitnessForm φ ψ
  swap₁ := by intro x y z; rw [flatWitnessForm_apply, flatWitnessForm_apply]; ring
  swap₂ := by intro x y z; rw [flatWitnessForm_apply, flatWitnessForm_apply]; ring

/-- The witness is exactly the printed cubic on the diagonal.
Article: main_krylov, apG:flat. -/
theorem flatWitnessCubic_diagonal (φ ψ : E →L[ℝ] ℝ) (x : E) :
    (flatWitnessCubic φ ψ).form x x x = 3 * Real.sqrt 3 * φ x * (ψ x)^2 := by
  change flatWitnessForm φ ψ x x x = _
  rw [flatWitnessForm_apply]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The printed cubic has sharp budget two on the real unit disk.
Article: main_krylov, apG:flat.
Proof: the nonnegative gap is (1-3x²)²(4-3x²). -/
theorem flat_witness_disk_bound (c s : ℝ) (hcs : c^2+s^2 ≤ 1) :
    |3 * Real.sqrt 3 * c * s^2| ≤ 2 := by
  have hu : c^2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hss : (s^2)^2 ≤ (1-c^2)^2 := pow_le_pow_left₀ (sq_nonneg s) (by linarith) 2
  have hgap := mul_nonneg (sq_nonneg (1-3*c^2)) (by nlinarith : 0 ≤ 4-3*c^2)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hmul := mul_le_mul_of_nonneg_left hss (by positivity : 0 ≤ 27*c^2)
  have hbound : (3 * Real.sqrt 3 * c * s^2)^2 ≤ (2 : ℝ)^2 := by
    have hid : (3 * Real.sqrt 3 * c * s^2)^2 = 27*c^2*(s^2)^2 := by nlinarith [sq_nonneg (Real.sqrt 3 * c * s^2)]
    rw [hid]
    nlinarith only [hgap, hmul]
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp (by simpa only [sq_abs] using hbound)

/-- Two true orthonormal directions make the genuine witness admissible for
the original diagonal spectral budget two. Article: main_krylov, apG:flat. -/
theorem flatWitnessCubic_diagonal_bound (e h : E) (he : ‖e‖ = 1) (hh : ‖h‖ = 1)
    (heh : inner ℝ e h = 0) :
    ∀ x : E, ‖x‖ = 1 →
      |(flatWitnessCubic (innerSL ℝ e) (innerSL ℝ h)).form x x x| ≤ 2 := by
  intro x hx
  have hc := orthonormal_pair_coordinates e h x he hh heh
  rw [hx, one_pow] at hc
  rw [flatWitnessCubic_diagonal]
  exact flat_witness_disk_bound _ _ hc

end
end krylov.Tensor
