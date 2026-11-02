import krylov.Completion.WindowTrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, complete original window feasibility/refutation.
Use: prove exactly when the genuine physical window completion class is
nonempty, without presuming either positive shifted old block or range condition.
Source: original physical spectral compressions and the proved necessary and
sufficient singular-Schur physical completion criterion (Albert69).
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The original known-data spectral window feasibility conditions, including
both actual singular ranges and the order of the true Schur endpoints.
Use: an empty consistency interval is a genuine data refutation.
Article: main_krylov, thm:radau. -/
def windowCurvatureConditions (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) : Prop :=
  ∃ hlo : (T-mu • (Sᵀ*S)).PosSemidef,∃ hhi : (L • (Sᵀ*S)-T).PosSemidef,
    (LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin) ∧
    (LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range (L • (Sᵀ*S)-T).mulVecLin) ∧
    mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
      (Sᵀ*crossColumn d)) 0 0≤
      L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
        (Sᵀ*crossColumn d)) 0 0

/-- Every actual physical completion derives both original shifted-old-model
positive forms, rather than assuming their feasibility in advance.
Use: reject any original window data failing either known spectral form.
Article: main_krylov, thm:radau, necessity of both compressed spectral inequalities.
Proof: compress each genuine physical nonnegative spectral pencil by the true
stored columns and substitute the observed original compressed model. -/
theorem window_completion_shifted_forms
    (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A∈windowCurvatureCompletions S d T mu L) :
    (T-mu • (Sᵀ*S)).PosSemidef ∧ (L • (Sᵀ*S)-T).PosSemidef := by
  obtain ⟨_,hAl,hAh,hT,_⟩ := hA
  constructor
  · have h := hAl.conjTranspose_mul_mul_same S
    simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hT] using h
  · have h := hAh.conjTranspose_mul_mul_same S
    simpa only [conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hT] using h

/-- The original actual physical window completion class is nonempty exactly
when all four printed known-data feasibility conditions hold.
Use: every failure, including either singular-range failure or reversed true
Schur endpoints, makes the entire original matrix scenario class empty.
Article: main_krylov, thm:radau, full feasibility and otherwise-empty clauses.
Proof: any actual matrix derives both shifted positive old forms; the genuine
singular-Schur necessity then derives both range conditions and endpoint order.
Conversely the known-data conditions construct an actual lower endpoint matrix
by the proved original physical completion equivalence. -/
theorem window_completion_feasible_iff
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L) :
    (windowCurvatureCompletions S d T mu L).Nonempty ↔ windowCurvatureConditions S d T mu L := by
  constructor
  · rintro ⟨A,hA⟩
    obtain ⟨hlo,hhi⟩ := window_completion_shifted_forms S d T mu L A hA
    obtain ⟨hAs,hAl,hAh,hT,hzero⟩ := hA
    have he := (window_curvature_completion_iff S hS d hd T mu L
      (d ⬝ᵥ (A*ᵥ d)) hmuL hlo hhi).mp ⟨A,hAs,hAl,hAh,hT,hzero,rfl⟩
    obtain ⟨hrl,hrh,hcl,hch⟩ := he
    rw [scaled_cross_range _ _ (neg_ne_zero.mpr hmu.ne')] at hrl
    rw [scaled_cross_range _ _ (hmu.trans_le hmuL).ne'] at hrh
    exact ⟨hlo,hhi,hrl,hrh,hcl.trans hch⟩
  · rintro ⟨hlo,hhi,hrl,hrh,horder⟩
    have hrl' : LinearMap.range ((-mu) • (Sᵀ*crossColumn d)).mulVecLin≤LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin := by
      rw [scaled_cross_range _ _ (neg_ne_zero.mpr hmu.ne')]
      exact hrl
    have hrh' : LinearMap.range (L • (Sᵀ*crossColumn d)).mulVecLin≤LinearMap.range (L • (Sᵀ*S)-T).mulVecLin := by
      rw [scaled_cross_range _ _ (hmu.trans_le hmuL).ne']
      exact hrh
    obtain ⟨A,hAs,hAl,hAh,hT,hzero,_⟩ :=
      (window_curvature_completion_iff S hS d hd T mu L _ hmuL hlo hhi).mpr ⟨hrl',hrh',le_rfl,horder⟩
    exact ⟨A,hAs,hAl,hAh,hT,hzero⟩

end
end krylov.Completion
