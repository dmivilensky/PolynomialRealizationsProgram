import krylov.Completion.PhysicalDampingMinimax
import Mathlib.Analysis.Matrix.Order
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), physical spectral damping bound.
Use: derive the original class condition-ratio bound from actually attained
endpoint matrices in the genuine positive spectral completion family.
Source: true physical spectral quadratic forms and scalar arithmetic damping
minimax; no condition-ratio or endpoint band assumption is supplied separately.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.OneGradient
variable {n : ℕ}

/-- Every genuine attained curvature interval inside a positive physical
spectral matrix band has the original class-wide minimax damping bound.
Use: arithmetic Gauss--Radau damping never exceeds (kappa-1)/(kappa+1).
Article: main_krylov, thm:dcs(c).
Proof: evaluate the true lower and upper attained physical endpoint matrices
on the actual direction. Their real spectral pencils give mu*D≤lo and
hi≤L*D. Positive scalar cross multiplication then proves the printed ratio bound. -/
theorem physical_damping_band
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (lo hi mu L : ℝ)
    (hmu : 0<mu) (hmuL : mu≤L) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi)
    (hband : ∀ A∈C,(A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef) :
    (hi-lo)/(hi+lo)≤(L-mu)/(L+mu) := by
  obtain ⟨Alo,hAlo,hclo⟩ := (hrange lo).mpr ⟨le_rfl,horder⟩
  obtain ⟨Ahi,hAhi,hchi⟩ := (hrange hi).mpr ⟨horder,le_rfl⟩
  have hlow := (hband Alo hAlo).1.dotProduct_mulVec_nonneg d
  have hhigh := (hband Ahi hAhi).2.dotProduct_mulVec_nonneg d
  simp only [star_trivial,sub_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul,hclo] at hlow
  simp only [star_trivial,sub_mulVec,smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul,hchi] at hhigh
  have hL : 0<L := hmu.trans_le hmuL
  apply (div_le_div_iff₀ (by linarith : 0<hi+lo) (add_pos hL hmu)).mpr
  nlinarith [mul_nonneg hL.le hlow,mul_nonneg hmu.le hhigh]

/-- The actual arithmetic endpoint estimate controls every genuine physical
completion by the original class-wide spectral contraction factor.
Use: apply directly to the real observed Gauss--Radau DC policy.
Article: main_krylov, thm:dcs(c), |epsilonHat|≤rho_kappa.
Proof: the physical endpoint maximum is attained at the arithmetic estimate;
its actual unique minimax value has the proved positive-band bound. -/
theorem physical_arithmetic_damping_bound
    (C : Set (Matrix (Fin n) (Fin n) ℝ)) (d : Fin n → ℝ) (q lo hi mu L : ℝ)
    (hq : 0<q) (hmu : 0<mu) (hmuL : mu≤L) (hlo : 0<lo) (horder : lo≤hi)
    (hrange : ∀ c : ℝ,(∃ A∈C,d ⬝ᵥ (A*ᵥ d)=c) ↔ c∈Set.Icc lo hi)
    (hband : ∀ A∈C,(A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A∈C) :
    |1-physicalTrialLength d q A/arithmeticEstimate (q/hi) (q/lo)|≤(L-mu)/(L+mu) := by
  have ha : 0<q/hi := div_pos hq (hlo.trans_le horder)
  have hab : q/hi≤q/lo := div_le_div_of_nonneg_left hq.le hlo horder
  have hw := physical_damping_worst C d q lo hi hq hlo horder hrange
    (arithmeticEstimate (q/hi) (q/lo)) (arithmetic_estimate_attains ha hab).1
  have hvalue := (arithmetic_estimate_attains ha hab).2.trans
    (harmonic_physical_curvature hlo (hlo.trans_le horder) hq).2
  exact ((hw.2 ⟨A,hA,rfl⟩).trans hvalue.le).trans
    (physical_damping_band C d lo hi mu L hmu hmuL hlo horder hrange hband)

end
end krylov.Completion
