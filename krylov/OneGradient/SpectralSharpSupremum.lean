import krylov.OneGradient.SpectralSharpFamily
import krylov.OneGradient.FibreMinimax
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b) and cor:quant(a), original uniform sharpness.
Use: take exact suprema over real full-atom spectral references and transfer
them to every actual span-restricted one-gradient method on real scenarios.
Source: actual irreducible limiting references, strict physical ratio bounds,
harmonic scalar minimax and the genuine two-endpoint physical adversary.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Methods

/-- The condition-ratio coefficient equals the source's spectral-radius form.
Use: write the exact uniform coefficient in the original mu and L units.
Article: main_krylov, cor:quant(a).
Proof: clear the positive original endpoints and their positive sum. -/
theorem spectral_condition_coefficient {mu upper : ℝ} (hmu : 0 < mu) (hmuL : mu < upper) :
    (upper/mu-1)/(upper/mu+1)=(upper-mu)/(upper+mu) := by
  have hs : 0 < upper+mu := by linarith
  field_simp

private theorem ratio_coefficient_lt {a b : ℝ} (ha : 1≤a) (hab : a < b) :
    (a-1)/(a+1) < (b-1)/(b+1) := by
  have hpa : 0 < a+1 := by linarith
  have hpb : 0 < b+1 := by linarith
  apply (div_lt_div_iff₀ hpa hpb).mpr
  nlinarith

private theorem ratio_coefficient_gap {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    (b-1)/(b+1)-(a-1)/(a+1)≤b-a := by
  have hpa : 0 < a+1 := by linarith
  have hpb : 0 < b+1 := by linarith
  have he : (b-1)/(b+1)-(a-1)/(a+1)=2*(b-a)/((b+1)*(a+1)) := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (mul_pos hpb hpa)).mpr
  have hden : 2≤(b+1)*(a+1) := by nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ha)]
  have hh := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hab)
  nlinarith

/-- The exact supremum of actual original information ratios is the full
spectral condition ratio, in every fixed dimension at least two.
Use: the extremum is over physical matrices and gradients, not abstract intervals.
Article: main_krylov, s5:fibre(b), sup r=kappa.
Proof: every actual ratio is strictly smaller. The proved genuine irreducible
family gives an actual ratio above each proposed smaller upper bound. -/
theorem spectral_prior_ratio_isLUB (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu < upper) (n : ℕ) :
    IsLUB (Set.range (fun P : SpectralPriorReference n mu upper => spectralPriorRatio P)) (upper/mu) := by
  constructor
  · rintro _ ⟨P,rfl⟩
    exact (spectral_prior_ratio_bounds P hmu).2.2.le
  · intro b hb
    by_contra h
    have hlt : b < upper/mu := lt_of_not_ge h
    obtain ⟨q,_,_,P,_,_,_,hr,_⟩ := spectral_fibre_sharp_references mu upper hmu hmuL n
      (upper/mu-b) (sub_pos.mpr hlt)
    have hub := hb (Set.mem_range_self P)
    linarith

/-- Every genuine original information fibre has a strictly smaller harmonic
coefficient than the uniform spectral value; it is nonnegative even when collapsed.
Use: no real full-atom reference attains the sharp global spectral coefficient.
Article: main_krylov, cor:quant(a), nonattainment by a reference.
Proof: insert the actual reciprocal-endpoint ratio formula and use strict
monotonicity of the scalar harmonic coefficient on ratios at least one. -/
theorem spectral_prior_coefficient_bounds {mu upper : ℝ} (hmu : 0 < mu) (hmuL : mu < upper)
    {n : ℕ} (P : SpectralPriorReference n mu upper) :
    0≤spectralPriorCoefficient P ∧ spectralPriorCoefficient P < (upper-mu)/(upper+mu) := by
  have hr := spectral_prior_ratio_bounds P hmu
  rw [spectral_prior_coefficient_ratio P hmu,← spectral_condition_coefficient hmu hmuL]
  exact ⟨div_nonneg (sub_nonneg.mpr hr.2.1) (by linarith [hr.2.1]),ratio_coefficient_lt hr.2.1 hr.2.2⟩

/-- The exact uniform supremum of original physical fixed-fibre harmonic
minimax coefficients is the source's (L-mu)/(L+mu).
Use: this quantifies over every genuine reference in each fixed dimension.
Article: main_krylov, cor:quant(a).
Proof: all actual fibre coefficients obey the strict upper bound. The genuine
small-coupling family approaches the condition ratio; the elementary scalar
coefficient gap bound transfers this to every smaller proposed coefficient. -/
theorem spectral_prior_coefficient_isLUB (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu < upper) (n : ℕ) :
    IsLUB (Set.range (fun P : SpectralPriorReference n mu upper => spectralPriorCoefficient P))
      ((upper-mu)/(upper+mu)) := by
  constructor
  · rintro _ ⟨P,rfl⟩
    exact (spectral_prior_coefficient_bounds hmu hmuL P).2.le
  · intro b hb
    by_contra h
    have hlt : b < (upper-mu)/(upper+mu) := lt_of_not_ge h
    obtain ⟨q,_,_,P,_,_,_,hr,_⟩ := spectral_fibre_sharp_references mu upper hmu hmuL n
      ((upper-mu)/(upper+mu)-b) (sub_pos.mpr hlt)
    have hbounds := spectral_prior_ratio_bounds P hmu
    have hgap := ratio_coefficient_gap hbounds.2.1 hbounds.2.2.le
    rw [spectral_condition_coefficient hmu hmuL,← spectral_prior_coefficient_ratio P hmu] at hgap
    have hub := hb (Set.mem_range_self P)
    linarith

/-- Every actual span-restricted one-gradient method has the original sharp
uniform spectral lower bound, with true constant-prefix physical matrices
and admissible real unobserved output matrices.
Use: the bound requires no CG consistency or smoothness of the competing method.
Article: main_krylov, cor:quant(a), arbitrary-method uniform lower bound.
Proof: actual endpoint adversaries give omega times every true fixed-fibre
coefficient. Its original spectral supremum forces every uniform guarantee
above rho_kappa times omega, including the zero output-radius case. -/
theorem spectral_prior_method_uniform_lower (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu < upper) (n : ℕ)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+2)))) (hm : OneGradientSpanRestricted method)
    {omega : ℝ} (homega : 0≤omega) (hsmall : omega≤1) (v : ℝ)
    (hv : ∀ P : SpectralPriorReference n mu upper,∀ b : ℝ,
      (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b-mu • 1).PosSemidef →
      (upper • 1-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b).PosSemidef →
      ∀ B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ,B.IsSymm →
        relativeBudget (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
          (B-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)≤omega →
        fibreScenarioError P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support method b B≤v) :
    ((upper-mu)/(upper+mu))*omega≤v := by
  have hf (P : SpectralPriorReference n mu upper) : omega*spectralPriorCoefficient P≤v := by
    let A := P.matrix
    let hA := P.positive
    let g := P.gradient
    let hg := P.gradient_ne_zero
    let hc := P.full_support
    let lo := spectralLowerPivot A hA g hg hc mu
    let hi := spectralUpperPivot A hA g hg hc upper
    have hne := spectral_prior_nonempty_fibre P
    obtain ⟨horder,hends,hband⟩ := spectral_fibre_endpoint_band A hA g hg hc mu upper hne
    have hgap := (spectral_fibre_endpoint_gaps A hA g hg hc mu upper hmu hne).1
    obtain ⟨b,hb,B,hB,hbudget,hbound⟩ := fibre_method_endpoint_lower A hA g hg hc method hm lo hi
      (by linarith) horder homega hsmall
    have hbband : (lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
        (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef := by
      rcases hb with h|h
      · rw [h]
        exact hends
      · rw [Set.mem_singleton_iff.mp h]
        exact hband
    exact hbound.trans (hv P b hbband.1 hbband.2 B hB hbudget)
  by_cases hz : omega=0
  · obtain ⟨q,_,_,P,_⟩ := spectral_fibre_sharp_references mu upper hmu hmuL n 1 (by norm_num)
    simpa only [hz,zero_mul,mul_zero] using hf P
  · have hw : 0 < omega := lt_of_le_of_ne homega (Ne.symm hz)
    have hub : v/omega∈upperBounds (Set.range (fun P : SpectralPriorReference n mu upper => spectralPriorCoefficient P)) := by
      rintro _ ⟨P,rfl⟩
      apply (le_div_iff₀ hw).mpr
      simpa only [mul_comm] using hf P
    exact (le_div_iff₀ hw).mp ((spectral_prior_coefficient_isLUB mu upper hmu hmuL n).2 hub)

end
end krylov.OneGradient
