import krylov.Correction.CompressionBound
import krylov.LinearAlgebra.PlanarAggregation
import krylov.LinearAlgebra.MatrixNormBounds

/-!
Article: main_krylov, thm:C and thm:C2(a), actual planar attaining operators.
Use: prove that the second-order operator constants are attained by symmetric
matrices satisfying the individual norm budgets, including degenerate profiles.
Source: reuse the proved common-plane aggregate formulas and Frobenius energy.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.LinearAlgebra chebyshev1
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} {n : ℕ}

/-- A rank-one planar terminal perturbation has exactly its scalar Frobenius budget.
Use: the same final attaining perturbation is admissible in both norm regimes.
Article: main_krylov, thm:C and thm:C2(a), E′=weeᵀ.
Proof: the already proved planar Frobenius energy is w², whose nonnegative
square root is precisely the nonnegative budget. -/
theorem planar_terminal_hsNorm (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) {w : ℝ} (hw : 0 ≤ w) :
    hsNorm (planarMatrix e h w 0 0)=w := by
  have hn := hsNorm_sq (planarMatrix e h w 0 0)
  rw [planar_hsSq e h he hh heh] at hn
  nlinarith [hsNorm_nonneg (planarMatrix e h w 0 0)]

/-- Common-plane increments and a rank-one terminal perturbation have their exact second-order norm.
Use: a single actual matrix construction supplies both norm-budget attainments.
Article: main_krylov, thm:C and thm:C2(a), planar residual calculation.
Proof: use the existing physical aggregate identities; the final rank-one
action adds in the same old direction, so the nonnegative coefficients add exactly. -/
theorem planar_correction_value (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (heK : ∀ i∈I, e∈K i) (hhK : ∀ i∈I, h∈(K i)ᗮ)
    (ω : ι → ℝ) (hω : ∀ i∈I, 0 ≤ ω i) (a b c w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) :
    let T := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (planarMatrix e h (ω i*a) (ω i*b) (ω i*c))
    let X := ∑ i∈I, (K i).starProjection (T i h)
    ‖(∑ i∈I, (K i).starProjection (T i ((K i).starProjection X)))+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h w 0 0) X‖ =
        (∑ i∈I, ω i)*b*((∑ i∈I, ω i)*a+w) := by
  -- All actual projected actions and the terminal action point along the same old direction.
  have hv := planar_aggregate_values I K e h he hh heh heK hhK ω a b c
  dsimp only at hv ⊢
  rw [hv.2.1,hv.1,planarMatrix_action]
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hhe : inner ℝ h e=0 := by rw [real_inner_comm]; exact heh
  simp only [real_inner_smul_right,hee,hhe,mul_one,mul_zero,zero_mul,
    add_zero,zero_smul]
  rw [← add_smul,norm_smul,he,mul_one,Real.norm_eq_abs]
  have hW : 0 ≤ ∑ i∈I, ω i := sum_nonneg hω
  rw [abs_of_nonneg (by positivity)]
  ring

/-- Actual symmetric spectral-budget matrices attain the full second-order constant K.
Use: the sharp compression estimate has an explicit witness in arbitrary old
subspaces sharing an old unit direction and an orthogonal terminal unit direction.
Article: main_krylov, thm:C, sharpness of ‖𝓛f̂‖≤K.
Proof: choose the proved scalar maximizing pair in the existing trace-zero
planar spectral witness and add the rank-one terminal perturbation. -/
theorem spectral_compression_attained (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (heK : ∀ i∈I, e∈K i) (hhK : ∀ i∈I, h∈(K i)ᗮ)
    (ω : ι → ℝ) (hω : ∀ i∈I, 0 ≤ ω i) {w : ℝ} (hw : 0 ≤ w) :
    ∃ D : ι → Matrix (Fin n) (Fin n) ℝ, ∃ F : Matrix (Fin n) (Fin n) ℝ,
      (∀ i∈I, (D i).IsSymm ∧ opNorm (D i) ≤ ω i) ∧ F.IsSymm ∧ opNorm F ≤ w ∧
      let T := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (D i)
      let X := ∑ i∈I, (K i).starProjection (T i h)
      ‖(∑ i∈I, (K i).starProjection (T i ((K i).starProjection X)))+
        Matrix.toEuclideanCLM (𝕜 := ℝ) F X‖ = sharpConstant (∑ i∈I, ω i) w := by
  -- Choose concrete trace-zero planar matrices at the proved scalar maximizer.
  let W := ∑ i∈I, ω i
  let a := maximizingComplement W w
  let b := maximizingCross W w
  have hW : 0 ≤ W := sum_nonneg hω
  obtain ⟨ha,hb,hab⟩ := maximizing_coordinates hW hw
  let D := fun i => planarMatrix e h (ω i*a) (ω i*b) (ω i*(-a))
  let F := planarMatrix e h w 0 0
  refine ⟨D,F,?_,planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
  · intro i hi
    refine ⟨planarMatrix_isSymm _ _ _ _ _,?_⟩
    dsimp only [D]
    rw [planarMatrix_scale,opNorm_smul,abs_of_nonneg (hω i hi)]
    have hs := planar_spectral_norm_le e h he hh heh (-a) b (by simpa only [neg_sq] using hab)
    have hs' : opNorm (planarMatrix e h a b (-a)) ≤ 1 := by simpa only [neg_neg] using hs
    exact (mul_le_mul_of_nonneg_left hs' (hω i hi)).trans_eq (mul_one _)
  · exact (spectral_le_hsNorm F).trans (planar_terminal_hsNorm e h he hh heh hw).le
  · have hv := planar_correction_value I K e h he hh heh heK hhK ω hω a b (-a) w ha hb hw
    dsimp only [D,F] at ⊢
    rw [hv]
    change W*b*(W*a+w)=W*b*(W*a+w)
    rfl

/-- Actual symmetric Frobenius-budget matrices attain the improved second-order constant.
Use: the √2 improvement comes with admissible increment and terminal witnesses,
including empty and zero-budget profiles in the same construction.
Article: main_krylov, thm:C2(a), sharpness of K(W,w)/√2.
Proof: keep the maximizing old diagonal and divide only the cross coefficient
by √2; the exact Frobenius energy is one and the actual planar residual scales accordingly. -/
theorem frobenius_compression_attained (I : Finset ι)
    (K : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n))) [∀ i, (K i).HasOrthogonalProjection]
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (heK : ∀ i∈I, e∈K i) (hhK : ∀ i∈I, h∈(K i)ᗮ)
    (ω : ι → ℝ) (hω : ∀ i∈I, 0 ≤ ω i) {w : ℝ} (hw : 0 ≤ w) :
    ∃ D : ι → Matrix (Fin n) (Fin n) ℝ, ∃ F : Matrix (Fin n) (Fin n) ℝ,
      (∀ i∈I, (D i).IsSymm ∧ hsNorm (D i) ≤ ω i) ∧ F.IsSymm ∧ hsNorm F ≤ w ∧
      let T := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (D i)
      let X := ∑ i∈I, (K i).starProjection (T i h)
      Real.sqrt 2 * ‖(∑ i∈I, (K i).starProjection (T i ((K i).starProjection X)))+
        Matrix.toEuclideanCLM (𝕜 := ℝ) F X‖ = sharpConstant (∑ i∈I, ω i) w := by
  -- Divide only the symmetric cross coefficient by the positive square root of two.
  let W := ∑ i∈I, ω i
  let a := maximizingComplement W w
  let b := maximizingCross W w / Real.sqrt 2
  have hW : 0 ≤ W := sum_nonneg hω
  obtain ⟨ha,hcross,hab⟩ := maximizing_coordinates hW hw
  have hs : (Real.sqrt 2)^2=(2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 ≤ b := div_nonneg hcross hr.le
  have hb₂ : 2*b^2=maximizingCross W w^2 := by
    dsimp only [b]
    rw [div_pow,hs]
    ring
  have hnorm : hsNorm (planarMatrix e h a b 0)=1 := by
    have ht := hsNorm_sq (planarMatrix e h a b 0)
    rw [planar_hsSq e h he hh heh,hb₂] at ht
    nlinarith [hsNorm_nonneg (planarMatrix e h a b 0)]
  let D := fun i => planarMatrix e h (ω i*a) (ω i*b) (ω i*0)
  let F := planarMatrix e h w 0 0
  refine ⟨D,F,?_,planarMatrix_isSymm _ _ _ _ _,(planar_terminal_hsNorm e h he hh heh hw).le,?_⟩
  · intro i hi
    refine ⟨planarMatrix_isSymm _ _ _ _ _,?_⟩
    dsimp only [D]
    rw [planarMatrix_scale,hsNorm_smul,abs_of_nonneg (hω i hi),hnorm,mul_one]
  · have hv := planar_correction_value I K e h he hh heh heK hhK ω hω a b 0 w ha hb hw
    dsimp only [D,F] at ⊢
    rw [hv]
    change Real.sqrt 2*(W*(maximizingCross W w/Real.sqrt 2)*(W*a+w))=
      W*maximizingCross W w*(W*a+w)
    field_simp


end
end krylov.Correction
