import krylov.LinearAlgebra.FrobeniusSupport
import krylov.LinearAlgebra.Compression
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.FinCases

/-!
Article: main_krylov, lem:aggregate, Frobenius compression loss.
Use: two orthogonal actual input directions spend independent Hilbert--Schmidt
energy; symmetry counts the cross block twice.
Source: reuse mathlib's finite Bessel inequality and the earlier article's hsSq/hsNorm.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Finset chebyshev1
open scoped Matrix InnerProductSpace BigOperators

/-- Two orthogonal unit directions collect at most the actual vector energy.
Use: apply Bessel's inequality to each physical matrix row.
Article: main_krylov, lem:aggregate, Frobenius compression proof.
Proof: form the actual two-vector orthonormal family and reuse finite Bessel. -/
theorem two_unit_bessel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x h w : E) (hx : ‖x‖ = 1) (hh : ‖h‖ = 1) (hxh : inner ℝ x h = 0) :
    (inner ℝ x w)^2 + (inner ℝ h w)^2 ≤ ‖w‖^2 := by
  have hhx : inner ℝ h x = 0 := by rw [real_inner_comm, hxh]
  have ho : Orthonormal ℝ (![x, h] : Fin 2 → E) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hx, hh, hxh, hhx]
  have hb := ho.sum_inner_products_le (s := Finset.univ) w
  simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using hb

/-- Two orthonormal actual inputs collect at most the full actual Hilbert--Schmidt energy.
Use: the Frobenius compression proof keeps both the forward and transposed cross actions.
Article: main_krylov, lem:aggregate, ‖Ex‖²+‖Eh‖²≤‖E‖_F².
Proof: apply the proved two-direction Bessel inequality to every actual row and sum. -/
theorem hs_two_actions {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (x h : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) (hh : ‖h‖ = 1) (hxh : inner ℝ x h = 0) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E x‖^2 +
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E h‖^2 ≤ hsSq E := by
  have hr : ∀ i, (E *ᵥ WithLp.ofLp x) i ^ 2 + (E *ᵥ WithLp.ofLp h) i ^ 2 ≤
      ∑ j, E i j ^ 2 := by
    intro i
    have hb := two_unit_bessel x h (WithLp.toLp 2 (fun j => E i j)) hx hh hxh
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      EuclideanSpace.real_norm_sq_eq, Matrix.mulVec] using hb
  -- Sum genuine row energies, with no choice of a matrix norm instance.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  exact sum_le_sum fun i _ => hr i

/-- A unit old-subspace direction pays twice for its actual symmetric cross action.
Use: the single-increment sharp Frobenius loss before aggregating budgets.
Article: main_krylov, lem:aggregate, Frobenius compression inequality.
Proof: two orthonormal physical inputs spend independent Hilbert--Schmidt energy;
projection Bessel and symmetry count the same cross entry in both actions. -/
theorem hs_compression_unit {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) [K.HasOrthogonalProjection]
    (h w : EuclideanSpace ℝ (Fin n)) (hh : h ∈ Kᗮ) (hn : ‖h‖ = 1)
    (hw : w ∈ K) (hwn : ‖w‖ = 1) :
    ‖K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E w)‖^2 +
      2 * (inner ℝ h (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E w))^2 ≤ hsSq E := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E
  have hsym : T.toLinearMap.IsSymmetric := by
    change (Matrix.toEuclideanLin E).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hE)
  have hperp : inner ℝ w h = 0 := (K.mem_orthogonal h).mp hh w hw
  have ht := hs_two_actions E w h hwn hn hperp
  have hp := projection_bessel K h hh hn (T w)
  have he : inner ℝ h (T w) = inner ℝ w (T h) := (real_inner_comm h (T w)).symm.trans (hsym w h)
  -- The forward cross action is the same actual scalar as the transposed action.
  have hc : |inner ℝ w (T h)| ≤ ‖T h‖ := by
    simpa only [Real.norm_eq_abs, hwn, one_mul] using norm_inner_le_norm (𝕜 := ℝ) w (T h)
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hc
  rw [sq_abs, ← he] at hs
  linarith

/-- Arbitrary old-subspace compressions retain twice the cross loss under a true Frobenius budget.
Use: the exact per-increment disk condition for the improved aggregated Frobenius estimate.
Article: main_krylov, lem:aggregate, ‖Yv‖²+2⟨x,v⟩²≤ω²‖v‖².
Proof: normalize the actual projected vector only when nonzero, apply the unit
compression theorem and rescale; its projection and the actual Frobenius norm give the budget. -/
theorem hs_compression_action {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) [K.HasOrthogonalProjection]
    (h : EuclideanSpace ℝ (Fin n)) (hh : h ∈ Kᗮ) (hn : ‖h‖ = 1)
    {ω : ℝ} (hω : hsNorm E ≤ ω) (v : EuclideanSpace ℝ (Fin n)) :
    ‖K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E (K.starProjection v))‖^2 +
      2 * (inner ℝ (K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E h)) v)^2 ≤
        ω^2 * ‖v‖^2 := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E
  let w := K.starProjection v
  have hsym : T.toLinearMap.IsSymmetric := by
    change (Matrix.toEuclideanLin E).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hE)
  have he : inner ℝ (K.starProjection (T h)) v = inner ℝ h (T w) := by
    rw [K.inner_starProjection_left_eq_right]
    exact hsym h w
  have hω0 : 0 ≤ ω := (hsNorm_nonneg E).trans hω
  have hbudget : hsSq E ≤ ω^2 := by
    rw [← hsNorm_sq]
    exact (sq_le_sq₀ (hsNorm_nonneg _) hω0).mpr hω
  have hproj := (sq_le_sq₀ (norm_nonneg w) (norm_nonneg v)).mpr (K.norm_starProjection_apply_le v)
  have hraw : ‖K.starProjection (T w)‖^2 + 2 * (inner ℝ h (T w))^2 ≤ hsSq E * ‖w‖^2 := by
    by_cases hw : w = 0
    · simp only [hw, map_zero, norm_zero, inner_zero_right, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        mul_zero, add_zero, le_refl]
    · let u := NormedSpace.normalize w
      have hu : u ∈ K := K.smul_mem _ (K.starProjection_apply_mem v)
      have hc := hs_compression_unit E hE K h u hh hn hu (NormedSpace.norm_normalize hw)
      have hy := congrArg (fun z => K.starProjection (T z)) (NormedSpace.norm_smul_normalize w)
      simp only [map_smul] at hy
      have hx := congrArg (fun z => inner ℝ h (T z)) (NormedSpace.norm_smul_normalize w)
      simp only [map_smul, real_inner_smul_right] at hx
      -- Rescale the actual normalized projected vector; no step length enters a denominator bound.
      rw [← hy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w), ← hx]
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖w‖)]
  rw [he]
  exact hraw.trans ((mul_le_mul_of_nonneg_right hbudget (sq_nonneg ‖w‖)).trans
    (mul_le_mul_of_nonneg_left hproj (sq_nonneg ω)))

/-- The actual projected cross action costs √2 in a symmetric Frobenius budget.
Use: the first sharp Frobenius aggregation bound applies to every genuine increment.
Article: main_krylov, lem:aggregate, √2‖P_lE_lh‖≤ω_l.
Proof: test the proved compression action on its actual cross vector, cancel
its squared norm only when nonzero, and take the nonnegative square root. -/
theorem hs_cross_norm {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) [K.HasOrthogonalProjection]
    (h : EuclideanSpace ℝ (Fin n)) (hh : h ∈ Kᗮ) (hn : ‖h‖ = 1)
    {ω : ℝ} (hω : hsNorm E ≤ ω) :
    Real.sqrt 2 * ‖K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E h)‖ ≤ ω := by
  let x := K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E h)
  have ha := hs_compression_action E hE K h hh hn hω x
  change ‖K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E (K.starProjection x))‖^2 +
    2 * (inner ℝ x x)^2 ≤ ω^2 * ‖x‖^2 at ha
  rw [real_inner_self_eq_norm_sq] at ha
  have hq : 2 * ‖x‖^2 ≤ ω^2 := by
    by_cases hz : ‖x‖ = 0
    · simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]; exact sq_nonneg ω
    · -- A nonzero actual cross vector permits cancellation of its strictly positive squared norm.
      apply (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero hz)).mp
      nlinarith [sq_nonneg ‖K.starProjection (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E (K.starProjection x))‖]
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    ((hsNorm_nonneg _).trans hω)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hq

end
end krylov.LinearAlgebra
