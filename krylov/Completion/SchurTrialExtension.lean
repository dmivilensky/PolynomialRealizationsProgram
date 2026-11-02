import krylov.Completion.ObservedHarmonicTrial
import krylov.Stability.ContDiffSpectralMatrix
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and s8:dcsdef, smooth Schur continuations.
Use: give literal rational continuations of the observed interval rules on
open inverse domains, also when nearby supplied data are infeasible or the
true information interval at the reference is collapsed.
Source: the original Schur endpoint formulas and standard smooth inversion.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra krylov.OneGradient krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The ordinary-inverse Schur continuation of the observed lower curvature.
Use: this rational expression is defined on arbitrary nearby observed data.
Article: main_krylov, thm:radau. -/
def schurLowerCurvature (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu : ℝ) : ℝ :=
  mu*(d ⬝ᵥ d)+mu^2*((Sᵀ*crossColumn d)ᵀ*(T-mu • (Sᵀ*S))⁻¹*(Sᵀ*crossColumn d)) 0 0

/-- The ordinary-inverse Schur continuation of the observed upper curvature.
Use: no feasibility test, pseudoinverse rank decision or endpoint ordering
is differentiated in the actual smooth continuation.
Article: main_krylov, thm:radau. -/
def schurUpperCurvature (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (upper : ℝ) : ℝ :=
  upper*(d ⬝ᵥ d)-upper^2*((Sᵀ*crossColumn d)ᵀ*(upper • (Sᵀ*S)-T)⁻¹*(Sᵀ*crossColumn d)) 0 0

/-- The smooth continuation of the original arithmetic endpoint-step rule.
Use: a real data-only Gauss--Radau estimate can remain smooth off feasibility.
Article: main_krylov, s8:dcsdef. -/
def schurArithmeticEstimate (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper q : ℝ) : ℝ :=
  q*((schurLowerCurvature S d T mu)⁻¹+(schurUpperCurvature S d T upper)⁻¹)/2

/-- The smooth continuation of the original harmonic endpoint-step trial.
Use: the single midpoint-curvature trial extends through collapsed intervals.
Article: main_krylov, thm:radau. -/
def schurHarmonicTrial (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper q : ℝ) : ℝ :=
  2*q/(schurLowerCurvature S d T mu+schurUpperCurvature S d T upper)

/-- Both actual observed curvature endpoints equal their literal rational
Schur continuations wherever the two observed shifted pencils are positive.
Use: identification includes collapsed information intervals and makes no
claim of global smoothness of total infimum/supremum rules at singular data.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: genuine shifted positivity discharges both range conditions and turns
the actual Moore--Penrose inverses into ordinary inverses. Physical feasibility
gives the true endpoint order, so the actual infimum and supremum are these ends. -/
theorem observed_endpoints_schur_extension
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (T-mu • (Sᵀ*S)).PosDef) (hhi : (upper • (Sᵀ*S)-T).PosDef)
    (hC : (windowCurvatureCompletions S d T mu upper).Nonempty) :
    observedLowerCurvature S d T mu upper=schurLowerCurvature S d T mu ∧
      observedUpperCurvature S d T mu upper=schurUpperCurvature S d T upper := by
  have hr (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef) :
      LinearMap.range (Sᵀ*crossColumn d).mulVecLin≤LinearMap.range A.mulVecLin := by
    intro z _
    refine ⟨A⁻¹*ᵥ z,?_⟩
    change A*ᵥ (A⁻¹*ᵥ z)=z
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]
  have he := observed_window_curvatures_schur S hS d hd T mu upper hmu hmuL
    hlo.posSemidef hhi.posSemidef (hr _ hlo) (hr _ hhi)
  rw [pseudoinverse_eq_inv _ _ (isUnit_iff_ne_zero.mpr hlo.det_pos.ne'),
    pseudoinverse_eq_inv _ _ (isUnit_iff_ne_zero.mpr hhi.det_pos.ne')] at he
  change observedWindowCurvatures S d T mu upper=Set.Icc
    (schurLowerCurvature S d T mu) (schurUpperCurvature S d T upper) at he
  obtain ⟨A,hA⟩ := hC
  have hmem : d ⬝ᵥ (A*ᵥ d)∈observedWindowCurvatures S d T mu upper := ⟨A,hA,rfl⟩
  rw [he] at hmem
  have horder := hmem.1.trans hmem.2
  exact ⟨by rw [observedLowerCurvature,he,csInf_Icc horder],
    by rw [observedUpperCurvature,he,csSup_Icc horder]⟩

/-- Both genuine observed interval rules equal their smooth Schur
continuations on every feasible positive-pencil window.
Use: arithmetic DC and harmonic XRFC choices share one endpoint dictionary.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: substitute the actual endpoint dictionary into their original scalar
rules; true physical endpoint positivity justifies the harmonic identity. -/
theorem observed_rules_schur_extension
    (S : Matrix (Fin n) (Fin p) ℝ) (hS : Function.Injective S.mulVec)
    (d : Fin n → ℝ) (hd : d∉LinearMap.range S.mulVecLin)
    (T : Matrix (Fin p) (Fin p) ℝ) (mu upper q : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (T-mu • (Sᵀ*S)).PosDef) (hhi : (upper • (Sᵀ*S)-T).PosDef)
    (hC : (windowCurvatureCompletions S d T mu upper).Nonempty) :
    observedArithmeticEstimate S d T mu upper q=schurArithmeticEstimate S d T mu upper q ∧
      observedHarmonicTrial S d T mu upper q=schurHarmonicTrial S d T mu upper q := by
  have he := observed_endpoints_schur_extension S hS d hd T mu upper hmu hmuL hlo hhi hC
  have hr := observed_window_curvature_range S hS d hd T mu upper hmu hmuL hC
  have hl : 0<schurLowerCurvature S d T mu := he.1 ▸ hr.1
  have hh : 0<schurUpperCurvature S d T upper := he.2 ▸ hr.1.trans_le hr.2.1
  constructor
  · simp only [observedArithmeticEstimate,arithmeticEstimate,schurArithmeticEstimate,he.1,he.2]
    ring
  · simp only [observedHarmonicTrial,harmonicTrial,schurHarmonicTrial,he.1,he.2]
    field_simp

end
end krylov.Completion
