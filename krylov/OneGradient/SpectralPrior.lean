import krylov.OneGradient.SpectralFibreRatio
import krylov.OneGradient.TrialMinimax
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b) and cor:quant(a), original spectral prior.
Use: quantify simultaneously over every genuine full-atom physical reference
of a fixed dimension in the given spectral class.
Source: original physical information fibres and their already proved closed
Schur endpoints, strict gap bounds and scalar harmonic minimax formula.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
variable {n : ℕ} {mu upper : ℝ}

/-- An original physical full-atom reference in the known spectral class.
Use: the uniform quantifier ranges over actual matrices and gradients, without
replacing the prior by arbitrary scalar information intervals.
Article: main_krylov, cor:quant(a). -/
structure SpectralPriorReference (n : ℕ) (mu upper : ℝ) where
  /-- Original physical reference matrix. -/
  matrix : Matrix (Fin (n+2)) (Fin (n+2)) ℝ
  /-- Genuine reference positivity. -/
  positive : matrix.PosDef
  /-- Original initial gradient. -/
  gradient : EuclideanSpace ℝ (Fin (n+2))
  /-- The initial gradient is nonzero. -/
  gradient_ne_zero : gradient≠0
  /-- Every physical spectral atom is active. -/
  full_support : (activeSpectralValues matrix positive.1 gradient).card=n+2
  /-- Actual lower spectral bound, including its boundary. -/
  lower_band : (matrix-mu • 1).PosSemidef
  /-- Actual upper spectral bound, including its boundary. -/
  upper_band : (upper • 1-matrix).PosSemidef

/-- The genuine final positive Lanczos coupling of the original reference.
Use: sharpness retains the source's actual beta.
Article: main_krylov, s5:fibre(b). -/
def spectralPriorCoupling (P : SpectralPriorReference n mu upper) : ℝ :=
  physicalJacobi P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support
    (Fin.castSucc (Fin.last n)) (Fin.last (n+1))

/-- The actual physical information ratio of an original spectral reference.
Use: all uniform extrema below retain the true measured fibre endpoints.
Article: main_krylov, s5:fibre(b) and cor:quant(a). -/
def spectralPriorRatio (P : SpectralPriorReference n mu upper) : ℝ :=
  let sigma := lastJacobiPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support-
    (lastInversePivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support)⁻¹
  (spectralUpperPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support upper-sigma)/
    (spectralLowerPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support mu-sigma)

/-- The true physical reciprocal-step harmonic minimax coefficient.
Use: subsequent uniform minimax statements use the original fixed-fibre value.
Article: main_krylov, cor:quant(a). -/
def spectralPriorCoefficient (P : SpectralPriorReference n mu upper) : ℝ :=
  let sigma := lastJacobiPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support-
    (lastInversePivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support)⁻¹
  intervalMinimaxValue
    (1/(spectralUpperPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support upper-sigma))
    (1/(spectralLowerPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support mu-sigma))

/-- The genuine original reference itself belongs to its physical spectral fibre.
Use: every endpoint-domain hypothesis follows from actual prior membership.
Article: main_krylov, s5:fibre(b).
Proof: completing at its actual measured last diagonal leaves the matrix equal
to the original reference, whose two real spectral bounds are stored. -/
theorem spectral_prior_nonempty_fibre (P : SpectralPriorReference n mu upper) :
    ∃ b : ℝ,(lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b).PosSemidef := by
  refine ⟨lastJacobiPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support,?_⟩
  simpa only [lanczosCompletion,sub_self,zero_smul,add_zero] using ⟨P.lower_band,P.upper_band⟩

/-- Every genuine spectral reference has its original ratio between one and
the strict global condition ratio, with a strictly positive actual coupling.
Use: the sharp global spectral ratio is never attained by a real reference.
Article: main_krylov, s5:fibre(b).
Proof: the original interval is ordered; its actual lower pivot gap exceeds
mu. The proved strict physical ratio theorem and true coupling positivity apply. -/
theorem spectral_prior_ratio_bounds (P : SpectralPriorReference n mu upper) (hmu : 0 < mu) :
    0 < spectralPriorCoupling P ∧ 1≤spectralPriorRatio P ∧ spectralPriorRatio P < upper/mu := by
  have hne := spectral_prior_nonempty_fibre P
  have horder := (spectral_fibre_endpoint_band P.matrix P.positive P.gradient P.gradient_ne_zero
    P.full_support mu upper hne).1
  have hgap := (spectral_fibre_endpoint_gaps P.matrix P.positive P.gradient P.gradient_ne_zero
    P.full_support mu upper hmu hne).1
  refine ⟨physical_jacobi_last_coupling_positive _ _ _ _ _,?_,
    spectral_fibre_ratio_strict _ _ _ _ _ mu upper hmu hne⟩
  dsimp only [spectralPriorRatio]
  apply (one_le_div (hmu.trans hgap)).mpr
  exact sub_le_sub_right horder _

/-- The original physical reciprocal-endpoint coefficient is precisely its
condition-ratio expression, including a collapsed information interval.
Use: pass the actual sharp fixed-fibre value to the original uniform prior.
Article: main_krylov, cor:quant(a).
Proof: true endpoint gaps are positive, so the exact scalar ratio identity
applies to their actual reciprocal CG lengths. -/
theorem spectral_prior_coefficient_ratio (P : SpectralPriorReference n mu upper) (hmu : 0 < mu) :
    spectralPriorCoefficient P=(spectralPriorRatio P-1)/(spectralPriorRatio P+1) := by
  have hne := spectral_prior_nonempty_fibre P
  obtain ⟨hl,hh⟩ := spectral_fibre_endpoint_gaps P.matrix P.positive P.gradient P.gradient_ne_zero
    P.full_support mu upper hmu hne
  have ho := (spectral_fibre_endpoint_band P.matrix P.positive P.gradient P.gradient_ne_zero
    P.full_support mu upper hne).1
  have hp := hmu.trans hl
  have hp' := hp.trans_le (sub_le_sub_right ho _)
  dsimp only [spectralPriorCoefficient,spectralPriorRatio]
  rw [interval_minimax_ratio (one_div_pos.mpr hp')]
  congr 2 <;> field_simp

end
end krylov.OneGradient
