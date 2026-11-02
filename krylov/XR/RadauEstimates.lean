import krylov.XR.RadauDomain
import krylov.XR.AlgorithmModel

/-!
Article: main_krylov, apG:radau-adequate, literal algorithm endpoints.
Use: identify the ordinary shifted-inverse coefficients in ModelStep with
the actual attained physical consistency interval and derive midpoint
adequacy. Source: the existing singular Schur completion theorem; no
ordered-interval or inverse-domain premise is hidden in a trial policy.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Completion krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The literal lower algorithm coefficient times squared direction norm
is the genuine physical ordinary-Schur curvature formula.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_lower_dictionary (s : Fin p → EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0) (T : Matrix (Fin p) (Fin p) ℝ) (mu : ℝ) :
    schurLowerCurvature (radauStepMatrix s) (WithLp.ofLp d) T mu=
      lowerConsistencyCoefficient s T d mu*‖d‖^2 := by
  have hD : WithLp.ofLp d ⬝ᵥWithLp.ofLp d=‖d‖^2 := by
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct] using
      real_inner_self_eq_norm_sq d
  rw [schurLowerCurvature,window_schur_correction,radauStepMatrix_coordinates,
    radauStepMatrix_crossGram,hD,lowerConsistencyCoefficient,add_mul,
    div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))]

/-- The literal upper algorithm coefficient has the same exact physical
Schur dictionary. Article: main_krylov, apG:radau-adequate. -/
theorem radau_upper_dictionary (s : Fin p → EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0) (T : Matrix (Fin p) (Fin p) ℝ) (upper : ℝ) :
    schurUpperCurvature (radauStepMatrix s) (WithLp.ofLp d) T upper=
      upperConsistencyCoefficient s T d upper*‖d‖^2 := by
  have hD : WithLp.ofLp d ⬝ᵥWithLp.ofLp d=‖d‖^2 := by
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct] using
      real_inner_self_eq_norm_sq d
  rw [schurUpperCurvature,window_schur_correction,radauStepMatrix_coordinates,
    radauStepMatrix_crossGram,hD,upperConsistencyCoefficient,sub_mul,
    div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))]

/-- Genuine feasible shifted-positive physical data give the literal
algorithm's ordered coefficients in the original spectral band. Every
physical completion has directional curvature inside these actual ends.
Article: main_krylov, apG:radau-adequate. -/
theorem radau_coefficients_feasible
    (s : Fin p → EuclideanSpace ℝ (Fin n))
    (hS : Function.Injective (radauStepMatrix s).mulVec)
    (d : EuclideanSpace ℝ (Fin n))
    (hd : WithLp.ofLp d∉LinearMap.range (radauStepMatrix s).mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper : ℝ) (hmu : 0<mu) (hband : mu≤upper)
    (hlo : (T-mu • ((radauStepMatrix s)ᵀ*radauStepMatrix s)).PosDef)
    (hhi : (upper • ((radauStepMatrix s)ᵀ*radauStepMatrix s)-T).PosDef)
    (hC : (windowCurvatureCompletions (radauStepMatrix s) (WithLp.ofLp d) T mu upper).Nonempty) :
    let lo := lowerConsistencyCoefficient s T d mu
    let hi := upperConsistencyCoefficient s T d upper
    mu≤lo ∧ lo≤hi ∧ hi≤upper ∧
      ∀ B∈windowCurvatureCompletions (radauStepMatrix s) (WithLp.ofLp d) T mu upper,
        lo*‖d‖^2 ≤ inner ℝ d (cgOperator B d) ∧ inner ℝ d (cgOperator B d)≤hi*‖d‖^2 := by
  have hd0 : d≠0 := by
    intro hz
    apply hd
    rw [hz,WithLp.ofLp_zero]
    exact ⟨0,map_zero _⟩
  have hD : 0<‖d‖^2 := pow_pos (norm_pos_iff.mpr hd0) _
  have hdd : WithLp.ofLp d ⬝ᵥWithLp.ofLp d=‖d‖^2 := by
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,dotProduct] using
      real_inner_self_eq_norm_sq d
  have he := observed_endpoints_schur_extension _ hS _ hd T mu upper hmu hband hlo hhi hC
  rw [radau_lower_dictionary s d hd0,radau_upper_dictionary s d hd0] at he
  have hr := observed_window_curvature_range _ hS _ hd T mu upper hmu hband hC
  have horder : lowerConsistencyCoefficient s T d mu≤upperConsistencyCoefficient s T d upper := by
    rw [he.1,he.2] at hr
    exact (mul_le_mul_iff_left₀ hD).mp hr.2.1
  have hlow : mu≤lowerConsistencyCoefficient s T d mu := by
    obtain ⟨B,hB,hBc⟩ := (hr.2.2 _).mpr ⟨le_rfl,hr.2.1⟩
    have hh := hB.2.1.dotProduct_mulVec_nonneg (WithLp.ofLp d)
    simp only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,
      dotProduct_smul,smul_eq_mul,hBc,hdd,he.1] at hh
    exact (mul_le_mul_iff_left₀ hD).mp (sub_nonneg.mp hh)
  have hhigh : upperConsistencyCoefficient s T d upper≤upper := by
    obtain ⟨B,hB,hBc⟩ := (hr.2.2 _).mpr ⟨hr.2.1,le_rfl⟩
    have hh := hB.2.2.1.dotProduct_mulVec_nonneg (WithLp.ofLp d)
    simp only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,
      dotProduct_smul,smul_eq_mul,hBc,hdd,he.2] at hh
    exact (mul_le_mul_iff_left₀ hD).mp (sub_nonneg.mp hh)
  refine ⟨hlow,horder,hhigh,?_⟩
  intro B hB
  have hc := (hr.2.2 _).mp ⟨B,hB,rfl⟩
  rw [he.1,he.2] at hc
  simpa only [Set.mem_Icc,cgOperator,Matrix.inner_toEuclideanCLM,star_trivial] using hc

/-- Any curvature in a positive spectral consistency interval satisfies
the sharp midpoint ratio bound. Article: apG:radau-adequate. -/
theorem radau_midpoint_ratio (mu upper lo hi c : ℝ) (hmu : 0<mu)
    (hlo : mu≤lo) (horder : lo≤hi) (hhi : hi≤upper) (hc : c≤hi) :
    0<(lo+hi)/2 ∧ c/((lo+hi)/2)≤2*hi/(hi+lo) ∧
      2*hi/(hi+lo)≤2*upper/(upper+mu) := by
  have hl := hmu.trans_le hlo
  have hh := hl.trans_le horder
  have hu := hh.trans_le hhi
  have hsum : 0<hi+lo := add_pos hh hl
  have hmid : 0<(lo+hi)/2 := by positivity
  refine ⟨hmid,?_,?_⟩
  · have he : c/((lo+hi)/2)=2*c/(hi+lo) := by field_simp;ring
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith) hsum.le
  · apply (div_le_div_iff₀ hsum (add_pos hu hmu)).mpr
    have hmul := mul_le_mul hlo hhi hh.le hl.le
    nlinarith only [hmul]

end
end krylov.XR
