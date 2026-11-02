import krylov.XR.RadauCompression
import krylov.Completion.SchurTrialExtension

/-!
Article: main_krylov, apG:radau-adequate, primitive physical feasibility.
Use: pass from the actual well-conditioned stored secants and measured
conjugacy to a genuine spectrally bounded completion preserving the true
new-direction curvature. Source: the explicit strict-interior extension;
feasibility and augmented independence are conclusions, not hypotheses.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence krylov.Secant
  krylov.Completion krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The physical transpose action is the original vector of observed
pairings. Article: main_krylov, apG:radau-adequate. -/
theorem radauStepMatrix_coordinates (s : Fin p → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    (radauStepMatrix s)ᵀ*ᵥWithLp.ofLp v=coordinates s v := by
  ext i
  simp only [radauStepMatrix,Matrix.mulVec,dotProduct,transpose_apply,coordinates,
    PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  exact Finset.sum_congr rfl fun a _=>mul_comm _ _

/-- A true lower synthesis bound is precisely a positive shifted physical
Gram. Article: main_krylov, apG:radau-adequate. -/
theorem radauStepMatrix_gain (s : Fin p → EuclideanSpace ℝ (Fin n)) (gamma : ℝ)
    (hgain : ∀ c : Fin p → ℝ,gamma*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2) :
    ((radauStepMatrix s)ᵀ*radauStepMatrix s-gamma • 1).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((isHermitian_conjTranspose_mul_self _).sub (by
      exact isHermitian_iff_isSymm.mpr (by simp only [IsSymm,transpose_smul,transpose_one])))
  intro c
  have he : c ⬝ᵥ (((radauStepMatrix s)ᵀ*radauStepMatrix s)*ᵥc)=‖combine s c‖^2 := by
    rw [←radauStepMatrix_combine,←real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_toLp_toLp,star_trivial,←Matrix.mulVec_mulVec,
      dotProduct_mulVec,vecMul_transpose]
  have hc : c ⬝ᵥc=‖WithLp.toLp 2 c‖^2 := by
    rw [←real_inner_self_eq_norm_sq,EuclideanSpace.inner_toLp_toLp,star_trivial]
  simpa only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul,he,hc] using sub_nonneg.mpr (hgain c)

/-- The actual desired augmented compression gives exactly the original
window equations, measured conjugacy and specified physical curvature.
Article: main_krylov, apG:radau-adequate. -/
theorem radauTarget_constraints (s : Fin p → EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin p) (Fin p) ℝ) (c : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : (radauStepMatrix (Fin.snoc s d))ᵀ*B*radauStepMatrix (Fin.snoc s d)=radauTarget T c) :
    (radauStepMatrix s)ᵀ*B*radauStepMatrix s=T ∧
      (radauStepMatrix s)ᵀ*ᵥ(B*ᵥWithLp.ofLp d)=0 ∧
      WithLp.ofLp d ⬝ᵥ (B*ᵥWithLp.ofLp d)=c := by
  rw [Matrix.mul_assoc,radauStepMatrix_image,radauStepMatrix_crossGram] at hB
  refine ⟨?_,?_,?_⟩
  · rw [Matrix.mul_assoc,radauStepMatrix_image,radauStepMatrix_crossGram]
    ext i j
    simpa only [crossGram,Fin.snoc_castSucc,radauTarget,Fin.lastCases_castSucc] using
      congrFun (congrFun hB i.castSucc) j.castSucc
  · rw [show B*ᵥWithLp.ofLp d=WithLp.ofLp (cgOperator B d) from rfl,
      radauStepMatrix_coordinates]
    ext i
    simpa only [crossGram,Fin.snoc_castSucc,Fin.snoc_last,radauTarget,
      Fin.lastCases_castSucc,Fin.lastCases_last,coordinates,Pi.zero_apply] using
      congrFun (congrFun hB i.castSucc) (Fin.last p)
  · have hh := congrFun (congrFun hB (Fin.last p)) (Fin.last p)
    simpa only [crossGram,Fin.snoc_last,radauTarget,Fin.lastCases_last,cgOperator,
      Matrix.inner_toEuclideanCLM,star_trivial] using hh

/-- For a unit new direction, sufficiently accurate actual secants have a
physical completion inside every strict spectral enclosure of the true
reference, with the true directional curvature unchanged.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_primitive_completion
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,‖s i‖=1)
    (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖=1)
    (mu a b upper sigma epsilon : ℝ) (hmu : mu<a) (hupper : b<upper)
    (hband : mu≤upper) (ha : 0<a) (hb : 0<b) (hsigma : 0<sigma)
    (hsigma₁ : sigma≤1) (he : 0≤epsilon)
    (hHlo : (H-a • 1).PosSemidef) (hHhi : (b • 1-H).PosSemidef)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),a*‖v‖^2 ≤ inner ℝ v (cgOperator H v))
    (hHnorm : ‖cgOperator H‖≤b)
    (hgain : ∀ c : Fin p → ℝ,sigma^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (hy : ∀ i,‖y i-cgOperator H (s i)‖≤epsilon)
    (ho : ∀ i,inner ℝ (y i) d=0)
    (hsmall : Real.sqrt p*epsilon≤a*sigma^2/2)
    (hsmalllo : (p+1 : ℕ)*epsilon<(a-mu)*(a*sigma^2/(2*b)))
    (hsmallhi : (p+1 : ℕ)*epsilon<(upper-b)*(a*sigma^2/(2*b))) :
    (radauTarget (latest (crossGram s y)) (inner ℝ (cgOperator H d) d)-mu •
      ((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d))).PosDef ∧
    (upper • ((radauStepMatrix (Fin.snoc s d))ᵀ*radauStepMatrix (Fin.snoc s d))-
      radauTarget (latest (crossGram s y)) (inner ℝ (cgOperator H d) d)).PosDef ∧
    ∃ B∈windowCurvatureCompletions (radauStepMatrix s) (WithLp.ofLp d)
        (latest (crossGram s y)) mu upper,
      WithLp.ofLp d ⬝ᵥ (B*ᵥWithLp.ofLp d)=inner ℝ d (cgOperator H d) := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hg : 0<a*sigma^2/(2*b) := by positivity
  have haug := radau_augmented_gain (cgOperator H) hsym s y d a b sigma epsilon ha hb
    hsigma hsigma₁ he hd hlower hHnorm hgain hy ho hsmall
  have hc := radau_nearby_compression (radauStepMatrix (Fin.snoc s d)) H hH
    (radauTarget (latest (crossGram s y)) (inner ℝ (cgOperator H d) d))
    (Matrix.isHermitian_iff_isSymm.mpr (radauTarget_isSymm _ (latest_isSymm _) _))
    mu a b upper _ _ hmu hupper hband hg (by positivity) hHlo hHhi
    (radauStepMatrix_gain _ _ haug) (by
      rw [radauStepMatrix_reference H hH]
      exact radauTarget_error _ hsym s y hs d hd epsilon he hy ho) hsmalllo hsmallhi
  obtain ⟨B,hBs,hBlo,hBhi,hBQ⟩ := hc.2.2
  obtain ⟨hBT,hBzero,hBc⟩ := radauTarget_constraints s d _ _ B hBQ
  refine ⟨hc.1,hc.2.1,B,⟨hBs,hBlo,hBhi,hBT,hBzero⟩,?_⟩
  exact hBc.trans (real_inner_comm _ _)

end
end krylov.XR
