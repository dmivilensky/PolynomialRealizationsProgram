import krylov.Completion.PhysicalTrialMinimax
import krylov.Completion.RayleighInterval
set_option autoImplicit false
/-!
Article: Theorem 4.3 [thm:radau] of krylov.tex.
Use: derive the unique midpoint-curvature minimax directly on the real
symmetric matrix completion class of the original window observations.
Source: actual singular Schur physical completion with both endpoints attained
and the proved physical searched-step interval minimax; no scalar scenario relaxation.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The original Gram-data matrix completion class of a physical window.
Use: the minimax ranges over genuine matrices with the exact original
spectral, model and direction-conjugacy constraints.
Article: main_krylov, thm:radau, C_G. -/
def windowCurvatureCompletions (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧
    Sᵀ*A*S=T ∧ Sᵀ*ᵥ (A*ᵥ d)=0}

/-- The actual arbitrary-window midpoint-curvature trial is the unique
minimax trial over all original physical matrix completions and all real trial lengths.
Use: the original source's window minimax is proved with genuine attained
physical endpoint scenarios, including singular and collapsed intervals.
Article: main_krylov, thm:radau, unique midpoint-curvature trial.
Proof: the true singular Schur theorem constructs every original physical
curvature. Its lower endpoint is positive because it is actually attained in
the positive spectral band along the genuine nonzero new direction. The proved
physical interval minimax therefore gives the exact value and its unique trial. -/
theorem window_trial_minimax
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L q : ℝ) (hmu : 0<mu) (hmuL : mu≤L) (hq : 0<q)
    (hlo : (T-mu • (Sᵀ*S)).PosSemidef) (hhi : (L • (Sᵀ*S)-T).PosSemidef)
    (hrlo : LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin)
    (hrhi : LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range (L • (Sᵀ*S)-T).mulVecLin)
    (horder : mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
        (Sᵀ*crossColumn d)) 0 0≤
      L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
        (Sᵀ*crossColumn d)) 0 0) :
    let cl := mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
      (Sᵀ*crossColumn d)) 0 0
    let ch := L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
      (Sᵀ*crossColumn d)) 0 0
    let C := windowCurvatureCompletions S d T mu L
    IsLeast {v : ℝ | ∃ t : ℝ,IsGreatest ((fun A => |1-t/physicalTrialLength d q A|) '' C) v}
      ((ch-cl)/(ch+cl)) ∧
      (∀ t : ℝ,(∀ A∈C,|1-t/physicalTrialLength d q A|≤(ch-cl)/(ch+cl)) ↔ t=2*q/(cl+ch)) := by
  let cl := mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*
    (Sᵀ*crossColumn d)) 0 0
  let ch := L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*
    (Sᵀ*crossColumn d)) 0 0
  let C := windowCurvatureCompletions S d T mu L
  have hrl : LinearMap.range ((-mu) • (Sᵀ*crossColumn d)).mulVecLin≤LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin := by
    rw [scaled_cross_range _ _ (neg_ne_zero.mpr hmu.ne')]
    exact hrlo
  have hrh : LinearMap.range (L • (Sᵀ*crossColumn d)).mulVecLin≤LinearMap.range (L • (Sᵀ*S)-T).mulVecLin := by
    rw [scaled_cross_range _ _ (hmu.trans_le hmuL).ne']
    exact hrhi
  have hrange (c : ℝ) : (∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc cl ch := by
    have he := window_curvature_completion_iff S hS d hd T mu L c hmuL hlo hhi
    constructor
    · rintro ⟨A,⟨hA,hAl,hAh,hT,hzero⟩,hcurv⟩
      exact (he.mp ⟨A,hA,hAl,hAh,hT,hzero,hcurv⟩).2.2
    · intro hc
      obtain ⟨A,hA,hAl,hAh,hT,hzero,hcurv⟩ := he.mpr ⟨hrl,hrh,hc⟩
      exact ⟨A,⟨hA,hAl,hAh,hT,hzero⟩,hcurv⟩
  have hcl : 0<cl := by
    obtain ⟨A,⟨_,hAl,_,_,_⟩,hcurv⟩ := (hrange cl).mpr ⟨le_rfl,horder⟩
    have hquad := hAl.dotProduct_mulVec_nonneg d
    simp only [star_trivial,sub_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
      dotProduct_smul,smul_eq_mul,hcurv] at hquad
    have hD := outside_range_direction_positive S d hd
    nlinarith [mul_pos hmu hD]
  exact physical_trial_minimax C d q cl ch hq hcl horder hrange

end
end krylov.Completion
