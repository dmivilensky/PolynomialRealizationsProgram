import krylov.Convergence.OneGradientSpectralFibreLower

/-!
Article: main_krylov, thm:LB, uniform spectral cubic lower bound.
Use: construct genuine smooth scalar cubic counterexamples for every
span-restricted one-gradient policy in every dimension at least two.
The true minimizer, true Hessian, spectral interval, canonical third
budget and reference CG error all concern the same constructed function.
Source: the actual fixed-fibre scalar theorem and the proved sharp
supremum over genuine irreducible spectral references.
-/

/-!
Article: krylov, Theorem E.16 [thm:LB].

Actual gradient-indistinguishable cubic twins give the arbitrary-method spectral/fixed-fibre
lower bound in the true minimizer metric; the native XRFC policy attains its leading
coefficient.
The formal auxiliary loss parameter is specialized to δ/10 so its tensor and metric factors
imply the exact printed 1±δ allowances. The genuine local minimum and true Hessian spectrum are
constructed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {μ L : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- A single genuine full-atom reference has fixed-information coefficient
arbitrarily close to the sharp spectral coefficient. Article: thm:LB. -/
theorem oneGradient_spectral_near_sharp_information
    (μ L : ℝ) (hμ : 0<μ) (hμL : μ<L) (n : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ P : SpectralPriorReference n μ L,(1-δ)*((L-μ)/(L+μ))<spectralPriorCoefficient P := by
  have hρ : 0<(L-μ)/(L+μ) := div_pos (sub_pos.mpr hμL) (by linarith)
  by_contra hn
  have hub : (1-δ)*((L-μ)/(L+μ))∈upperBounds
      (Set.range (fun P : SpectralPriorReference n μ L=>spectralPriorCoefficient P)) := by
    rintro x ⟨P,rfl⟩
    exact le_of_not_gt (fun hh=>hn ⟨P,hh⟩)
  have hh := (spectral_prior_coefficient_isLUB μ L hμ hμL n).2 hub
  nlinarith only [hh,mul_pos hδ hρ]

/-- Original uniform spectral one-gradient lower bound on genuine scalar
cubic sources. A fixed full-atom information family and the permitted
starting scale are chosen before the competing arbitrary data-only
policy. All source and true-metric properties are conclusions.
Article: main_krylov, thm:LB, uniform rho_kappa assertion. -/
theorem oneGradient_spectral_true_lower
    (μ L : ℝ) (hμ : 0<μ) (hμL : μ<L)
    (Mhat δ : ℝ) (hMhat : 0<Mhat) (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ P : SpectralPriorReference n μ L, ∃ s : ℝ,0<s ∧∀ h : ℝ,0<h → h<s →
      ∀ method : OneGradientMethod E,OneGradientSpanRestricted method →
      ∃ b : ℝ,∃ R : ℝ,0<R ∧
        ∃ w : OneGradientCubicLowerWitness method
          (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
          (h • P.gradient)
          (lastLanczosVector P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support)
          R ((1+δ)*Mhat) ((1-δ)*(Mhat/2)*((L-μ)/(L+μ))),
          ∀ i,μ*(1-δ)≤w.positive.1.eigenvalues i ∧w.positive.1.eigenvalues i≤L*(1+δ) := by
  obtain ⟨P,hP⟩ := oneGradient_spectral_near_sharp_information μ L hμ hμL n (δ/2) (half_pos hδ)
  obtain ⟨s,hs,hsource⟩ := oneGradient_spectral_fibre_true_lower P hμ hμL.le Mhat (δ/2) hMhat
    (half_pos hδ) (by linarith)
  have hρ : 0≤(L-μ)/(L+μ) := div_nonneg (sub_nonneg.mpr hμL.le) (by linarith)
  have hfactor : (1-δ)*((L-μ)/(L+μ))≤(1-δ/2)*spectralPriorCoefficient P := by
    have hh := mul_le_mul_of_nonneg_left hP.le (by linarith : 0≤1-δ/2)
    have hp : 0≤δ^2*((L-μ)/(L+μ)) := mul_nonneg (sq_nonneg _) hρ
    nlinarith only [hh,hp]
  refine ⟨P,s,hs,?_⟩
  intro h hh hhsmall method hmeth
  obtain ⟨b,hb,R,hR,w,hclose,hband⟩ := hsource h hh hhsmall method hmeth
  have hB : (1+δ/2)*Mhat≤(1+δ)*Mhat := by gcongr;linarith
  have hK : (1-δ)*(Mhat/2)*((L-μ)/(L+μ))≤(1-δ/2)*(Mhat/2)*spectralPriorCoefficient P := by
    nlinarith only [mul_le_mul_of_nonneg_right hfactor (by positivity : 0≤Mhat/2)]
  let w' := w.weaken hB hK
  refine ⟨b,R,hR,w',?_⟩
  intro i
  have hl := (hband i).1
  have hu := (hband i).2
  have hL : 0<L := hμ.trans hμL
  constructor <;> dsimp only [w',OneGradientCubicLowerWitness.weaken]
  · nlinarith only [hl,mul_pos hμ hδ]
  · nlinarith only [hu,mul_pos hL hδ]

end
end krylov.Convergence
