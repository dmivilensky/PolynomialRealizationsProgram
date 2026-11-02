import krylov.XR.RadauAugmentation
import krylov.Completion.SpectralExtension

/-!
Article: main_krylov, apG:radau-adequate, actual nearby compression.
Use: build the real augmented step frame and its desired symmetric Gram
with measured latest block, zero conjugacy cross block and unchanged true
new-direction curvature. Its discrepancy from the genuine reference Gram
is bounded entry by entry by the actual secant error.
Source: exact finite synthesis and observed latest-information identities.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The actual rectangular physical matrix of arbitrary step columns.
Article: main_krylov, apG:radau-adequate. -/
def radauStepMatrix (s : Fin p → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin p) ℝ :=
  fun a i=>s i a

/-- Physical matrix action is exactly the original finite synthesis.
Article: main_krylov, apG:radau-adequate. -/
theorem radauStepMatrix_combine (s : Fin p → EuclideanSpace ℝ (Fin n)) (c : Fin p → ℝ) :
    WithLp.toLp 2 (radauStepMatrix s*ᵥ c)=combine s c := by
  ext a
  simp only [radauStepMatrix,Matrix.mulVec,dotProduct,combine,WithLp.ofLp_sum,
    WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl fun i _=>mul_comm _ _

/-- Actual rectangular step Gram dictionary. Article: apG:radau-adequate. -/
theorem radauStepMatrix_crossGram (s y : Fin p → EuclideanSpace ℝ (Fin n)) :
    (radauStepMatrix s)ᵀ*radauStepMatrix y=crossGram s y := by
  ext i j
  simp only [crossGram,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    radauStepMatrix,Matrix.mul_apply,transpose_apply]
  exact Finset.sum_congr rfl fun a _=>mul_comm _ _

/-- The original actual operator maps each real step column separately.
Article: main_krylov, apG:radau-adequate. -/
theorem radauStepMatrix_image (H : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) :
    H*radauStepMatrix s=radauStepMatrix (fun i=>cgOperator H (s i)) := by
  ext a i
  rfl

/-- Exact physical/reference Gram dictionary. Article: apG:radau-adequate. -/
theorem radauStepMatrix_reference (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) :
    (radauStepMatrix s)ᵀ*H*radauStepMatrix s=localReferenceGram (cgOperator H) s := by
  rw [Matrix.mul_assoc,radauStepMatrix_image,radauStepMatrix_crossGram]
  ext i j
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) (s i) (s j) |>.symm

/-- The literal desired augmented model: latest old block, zero cross
block and unchanged actual reference directional energy. Article: apG:radau-adequate. -/
def radauTarget (T : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) : Matrix (Fin (p+1)) (Fin (p+1)) ℝ :=
  fun i j=>Fin.lastCases (Fin.lastCases c (fun _=>0) j)
    (fun a=>Fin.lastCases 0 (fun b=>T a b) j) i

/-- The actual desired block form is symmetric. Article: apG:radau-adequate. -/
theorem radauTarget_isSymm (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.IsSymm) (c : ℝ) :
    (radauTarget T c).IsSymm := by
  ext i j
  refine Fin.lastCases ?_ (fun i=>?_) i
  · refine Fin.lastCases ?_ (fun j=>?_) j <;> simp [radauTarget]
  · refine Fin.lastCases ?_ (fun j=>?_) j
    · simp [radauTarget]
    · simpa only [transpose_apply,radauTarget,Fin.lastCases_castSucc] using hT.apply i j

/-- The desired block differs from the original true augmented reference
only by the measured secant error. It preserves the new diagonal exactly.
Article: main_krylov, apG:radau-adequate. -/
theorem radauTarget_error (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : H.toLinearMap.IsSymmetric) (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (hs : ∀ i,‖s i‖=1) (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖=1)
    (epsilon : ℝ) (he : 0≤epsilon) (hy : ∀ i,‖y i-H (s i)‖≤epsilon)
    (ho : ∀ i,inner ℝ (y i) d=0) :
    ‖radauTarget (latest (crossGram s y)) (inner ℝ (H d) d)-
      localReferenceGram H (Fin.snoc s d)‖≤(p+1 : ℕ)*epsilon := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ he
  intro i j
  refine Fin.lastCases ?_ (fun i=>?_) i
  · refine Fin.lastCases ?_ (fun j=>?_) j
    · simpa only [Matrix.sub_apply,radauTarget,Fin.lastCases_last,localReferenceGram,
        crossGram,Fin.snoc_last,sub_self,abs_zero] using he
    · have hh := radau_reference_cross H s y d hd epsilon hy ho j
      have hsym : inner ℝ (H (s j)) d=inner ℝ (H d) (s j) := by
        calc
          _=inner ℝ (s j) (H d) := hH _ _
          _=_ := real_inner_comm _ _
      simpa only [Matrix.sub_apply,radauTarget,Fin.lastCases_last,Fin.lastCases_castSucc,
        localReferenceGram,crossGram,Fin.snoc_last,Fin.snoc_castSucc,zero_sub,abs_neg,
        ←hsym] using hh
  · refine Fin.lastCases ?_ (fun j=>?_) j
    · simpa only [Matrix.sub_apply,radauTarget,Fin.lastCases_last,Fin.lastCases_castSucc,
        localReferenceGram,crossGram,Fin.snoc_last,Fin.snoc_castSucc,zero_sub,abs_neg] using
        radau_reference_cross H s y d hd epsilon hy ho i
    · have hh := norm_inner_le_norm (𝕜 := ℝ) (s (min i j)) (y (max i j)-H (s (max i j)))
      rw [hs,one_mul,Real.norm_eq_abs] at hh
      have hh' := hh.trans (hy (max i j))
      have hentry : |(latest (crossGram s y)-localReferenceGram H s) i j|≤epsilon := by
        rw [local_latest_error_entry H hH s y]
        exact hh'
      simpa only [Matrix.sub_apply,radauTarget,Fin.lastCases_castSucc,
        localReferenceGram,crossGram,Fin.snoc_castSucc] using hentry

/-- Any actual positive synthesis gain proves rectangular physical
column independence. Article: main_krylov, apG:radau-adequate. -/
theorem radauStepMatrix_injective (s : Fin p → EuclideanSpace ℝ (Fin n))
    (gamma : ℝ) (hg : 0<gamma)
    (hgain : ∀ c : Fin p → ℝ,gamma*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2) :
    Function.Injective (radauStepMatrix s).mulVec := by
  intro a b hab
  have hz : radauStepMatrix s*ᵥ (a-b)=0 := by rw [mulVec_sub,hab,sub_self]
  have hh := hgain (a-b)
  have hs : combine s (a-b)=0 := by rw [←radauStepMatrix_combine,hz,WithLp.toLp_zero]
  simp only [hs,norm_zero,zero_pow (by decide : 2≠0)] at hh
  have hn : ‖WithLp.toLp 2 (a-b)‖=0 := by
    have hm : gamma*‖WithLp.toLp 2 (a-b)‖^2=0 :=
      le_antisymm hh (mul_nonneg hg.le (sq_nonneg _))
    have hz' := (mul_eq_zero.mp hm).resolve_left hg.ne'
    nlinarith only [hz']
  exact sub_eq_zero.mp ((WithLp.toLp_injective 2) (norm_eq_zero.mp hn))

end
end krylov.XR
