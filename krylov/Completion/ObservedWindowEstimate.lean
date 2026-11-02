import krylov.Completion.WindowFeasibility
import krylov.Completion.ActionWindowInterval
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef, one original known-data window estimate.
Use: implement the arithmetic step estimate from the actual observed S,T,d,
class spectral bounds and observed descent pairing, before any tilted solve.
Source: genuine attained physical window completion, exact singular-Schur
curvature range and the proved scalar arithmetic estimate; all are reused.
-/

namespace krylov.Completion
noncomputable section
open Matrix Set krylov.LinearAlgebra krylov.OneGradient
variable {n p : ℕ}

/-- All physical directional curvatures consistent with the original observed
window and class bounds, defined solely from those known data.
Use: original data-only policy construction retains the entire physical class.
Article: main_krylov, s8:dcsdef and thm:radau. -/
def observedWindowCurvatures (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) : Set ℝ :=
  {c | ∃ A∈windowCurvatureCompletions S d T mu L,d ⬝ᵥ (A*ᵥ d)=c}

/-- The lower original observed curvature endpoint as a total data-only rule.
Use: no unknown reference matrix or selected feasible completion enters the estimate.
Article: main_krylov, s8:dcsdef. -/
def observedLowerCurvature (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) : ℝ :=
  sInf (observedWindowCurvatures S d T mu L)

/-- The upper original observed curvature endpoint as a total data-only rule.
Use: the exact Schur dictionary below computes this rule on every feasible source window.
Article: main_krylov, s8:dcsdef. -/
def observedUpperCurvature (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) : ℝ :=
  sSup (observedWindowCurvatures S d T mu L)

/-- The actual Gauss--Radau arithmetic-step policy read from original observed
data before the native DC tilted direction is formed.
Use: one rule applies to all feasible source windows, including singular
spectral pencils and collapsed information intervals.
Article: main_krylov, s8:dcsdef, alphaHat=(alphaLo+alphaHi)/2. -/
def observedArithmeticEstimate (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L q : ℝ) : ℝ :=
  arithmeticEstimate (q/observedUpperCurvature S d T mu L) (q/observedLowerCurvature S d T mu L)

/-- The single original known-data curvature set is the literal singular-Schur
closed interval, with both endpoints genuinely realized by physical matrices.
Use: identify the implemented policy's endpoints with the printed formulas,
without assuming nonsingular shifted models or a positive interval width.
Article: main_krylov, s8:dcsdef and thm:radau.
Proof: scale the actual cross-range tests, then apply the proved necessary and
sufficient genuine physical window completion theorem at every real curvature. -/
theorem observed_window_curvatures_schur
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (T-mu • (Sᵀ*S)).PosSemidef) (hhi : (L • (Sᵀ*S)-T).PosSemidef)
    (hrlo : LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin)
    (hrhi : LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range (L • (Sᵀ*S)-T).mulVecLin) :
    observedWindowCurvatures S d T mu L=Set.Icc
      (mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hlo.1*(Sᵀ*crossColumn d)) 0 0)
      (L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hhi.1*(Sᵀ*crossColumn d)) 0 0) := by
  have hrl : LinearMap.range ((-mu) • (Sᵀ*crossColumn d)).mulVecLin≤LinearMap.range (T-mu • (Sᵀ*S)).mulVecLin := by
    rw [scaled_cross_range _ _ (neg_ne_zero.mpr hmu.ne')]
    exact hrlo
  have hrh : LinearMap.range (L • (Sᵀ*crossColumn d)).mulVecLin≤LinearMap.range (L • (Sᵀ*S)-T).mulVecLin := by
    rw [scaled_cross_range _ _ (hmu.trans_le hmuL).ne']
    exact hrhi
  ext c
  change (∃ A∈windowCurvatureCompletions S d T mu L,d ⬝ᵥ (A*ᵥ d)=c) ↔ _
  have he := window_curvature_completion_iff S hS d hd T mu L c hmuL hlo hhi
  constructor
  · rintro ⟨A,⟨hA,hAl,hAh,hT,hzero⟩,hcurv⟩
    exact (he.mp ⟨A,hA,hAl,hAh,hT,hzero,hcurv⟩).2.2
  · intro hc
    obtain ⟨A,hA,hAl,hAh,hT,hzero,hcurv⟩ := he.mpr ⟨hrl,hrh,hc⟩
    exact ⟨A,⟨hA,hAl,hAh,hT,hzero⟩,hcurv⟩

/-- On every feasible source window the original known-data lower and upper
rules have an attained positive ordered range.
Use: actual observed arithmetic estimates have real positive endpoint steps;
feasibility derives all singular-Schur side conditions rather than assuming them.
Article: main_krylov, s8:dcsdef and thm:dcs(c).
Proof: a genuine feasible matrix supplies the shifted positive forms, both
singular ranges and endpoint order. Actual physical completion proves the
closed curvature range, whose true infimum and supremum are its endpoints.
The realized lower endpoint lies in the original positive spectral band. -/
theorem observed_window_curvature_range
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hC : (windowCurvatureCompletions S d T mu L).Nonempty) :
    let lo := observedLowerCurvature S d T mu L
    let hi := observedUpperCurvature S d T mu L
    0<lo ∧ lo≤hi ∧ ∀ c : ℝ,
      (∃ A∈windowCurvatureCompletions S d T mu L,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi := by
  obtain ⟨hl,hh,hrl,hrh,horder⟩ := (window_completion_feasible_iff S hS d hd T mu L hmu hmuL).mp hC
  have he := observed_window_curvatures_schur S hS d hd T mu L hmu hmuL hl hh hrl hrh
  have hlow : observedLowerCurvature S d T mu L=
      mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (T-mu • (Sᵀ*S)) hl.1*(Sᵀ*crossColumn d)) 0 0 := by
    rw [observedLowerCurvature,he,csInf_Icc horder]
  have hhigh : observedUpperCurvature S d T mu L=
      L*(d ⬝ᵥ d)-L^2*((Sᵀ*crossColumn d)ᵀ*pseudoinverse (L • (Sᵀ*S)-T) hh.1*(Sᵀ*crossColumn d)) 0 0 := by
    rw [observedUpperCurvature,he,csSup_Icc horder]
  have hrange (c : ℝ) : (∃ A∈windowCurvatureCompletions S d T mu L,d ⬝ᵥ (A*ᵥ d)=c) ↔
      c∈Set.Icc (observedLowerCurvature S d T mu L) (observedUpperCurvature S d T mu L) := by
    change c∈observedWindowCurvatures S d T mu L ↔ _
    rw [he,hlow,hhigh]
  have hle : observedLowerCurvature S d T mu L≤observedUpperCurvature S d T mu L := by rw [hlow,hhigh];exact horder
  refine ⟨?_,hle,hrange⟩
  obtain ⟨A,⟨_,hAl,_,_,_⟩,hcurv⟩ := (hrange _).mpr ⟨le_rfl,hle⟩
  have hquad := hAl.dotProduct_mulVec_nonneg d
  simp only [star_trivial,sub_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul,hcurv] at hquad
  have hD := outside_range_direction_positive S d hd
  nlinarith [mul_pos hmu hD]

end
end krylov.Completion
