import krylov.Correction.GatedSmallLine
import krylov.Correction.ObservedGateAcceptance

/-!
Article: main_krylov, thm:UCq, actual observed search domains.
Use: Derive genuine conjugacy inverses and exclude zero computed directions
from actual measured pairs, old projected gradients and positive spectral data.
Source: real cross-Gram entry errors, proved Neumann inverse conditioning
and the orthogonal projection identity for the actual observed span.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual unit-column observed cross Gram has dimension-times-relative-pair spectral error.
Use: Derive the actual ordinary-RFC search domains from original data.
Article: main_krylov, thm:UCq.
Proof: Each real entry is a pair-error pairing with a true unit column. Cauchy--Schwarz and the existing spectral/Frobenius comparison give the dimension factor.
-/
theorem unit_crossGram_error (s y : Fin p → E) (hs : ∀ i, ‖s i‖=1)
    {η : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η) :
    ‖crossGram y s-crossGram s s‖≤(p : ℝ)*η := by
  apply (spectral_le_hsNorm _).trans (hsNorm_le_dimension _ hη ?_)
  intro i j
  change |inner ℝ (y i) (s j)-inner ℝ (s i) (s j)|≤η
  rw [← inner_sub_left]
  have ht := norm_inner_le_norm (𝕜 := ℝ) (y i-s i) (s j)
  rw [Real.norm_eq_abs,hs,mul_one] at ht
  exact ht.trans (hy i)

/-- The true observed conjugacy solve is nonsingular whenever its genuine normalized Gram and pair-error allowances sum to one half.
Use: Derive the actual ordinary-RFC search domains from original data.
Article: main_krylov, thm:UCq.
Proof: Bound the actual normalized nonsymmetric cross Gram by the two real errors. The proved Neumann theorem gives its inverse domain; exact nonzero diagonal congruence then forces the original observed determinant nonzero.
-/
theorem normalized_observed_solve_unit (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η δ : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hG : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤δ)
    (hsmall : δ+(p : ℝ)*η≤1/2) : IsUnit (crossGram y s).det := by
  let D := diagonal (fun i => ‖s i‖⁻¹)
  let M := crossGram (rescaleWindow y (fun i => ‖s i‖⁻¹)) (unitWindow s)
  have hM : ‖M-1‖≤1/2 := by
    have ht := unit_crossGram_error (unitWindow s) (rescaleWindow y (fun i => ‖s i‖⁻¹))
      (unitWindow_norm s hs) hη (unitWindow_pair_error s y hs hy)
    have he : M-1=(M-crossGram (unitWindow s) (unitWindow s))+
        (crossGram (unitWindow s) (unitWindow s)-1) := by abel
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add ht hG).trans (by linarith))
  have hu := (near_identity_inverse M hM).1
  have he : M=D*(crossGram y s)*D := by
    ext i j
    simp only [M,D,unitWindow,rescaleWindow,crossGram,Matrix.diagonal_mul,Matrix.mul_diagonal,
      real_inner_smul_left,real_inner_smul_right]
    ring
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hn := isUnit_iff_ne_zero.mp hu
  apply hn
  rw [he,det_mul,det_mul,hz,mul_zero,zero_mul]

variable [FiniteDimensional ℝ E]

/-- A real reference-base gradient lying in the observed span is bounded by the true old projected residual with a condition-ratio-only constant.
Use: Derive the actual ordinary-RFC search domains from original data.
Article: main_krylov, thm:UCq.
Proof: Orthogonal projection identifies the genuine positive base energy with its old projected-gradient pairing. Apply actual Gram-conditioned analysis and synthesis bounds and cancel the positive lower endpoint and nonzero actual gradient norm.
-/
theorem observed_zero_direction_gradient_bound (s : Fin p → E) (H : E →L[ℝ] E) (g : E)
    {μ κ : ℝ} (hμ : 0<μ) (hκ : 0≤κ)
    (hcoerc : ∀ v : E, μ*‖v‖^2≤ inner ℝ v (H v)) (hH : ‖H‖≤κ*μ)
    (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (hspan : H g∈Submodule.span ℝ (Set.range s)) :
    ‖g‖≤4*κ*‖projectedResidual s g‖ := by
  have he := (Submodule.span ℝ (Set.range s)).starProjection_inner_eq_zero g (H g) hspan
  change inner ℝ (g-observedProjection s g) (H g)=0 at he
  rw [inner_sub_left] at he
  have hp := observedProjection_residual_bound s hG g
  have hi := (real_inner_le_norm (observedProjection s g) (H g)).trans
    (mul_le_mul hp (H.le_opNorm g) (norm_nonneg _) (by positivity))
  have hn := mul_le_mul_of_nonneg_left hH (by positivity : 0≤4*‖projectedResidual s g‖*‖g‖)
  have hc := hcoerc g
  by_cases hg : g=0
  · rw [hg,norm_zero]; positivity
  · have hgp := norm_pos_iff.mpr hg
    have ht : μ*‖g‖^2≤(4*κ*‖projectedResidual s g‖)*μ*‖g‖ := by nlinarith
    by_contra hh
    have hlt : 4*κ*‖projectedResidual s g‖<‖g‖ := lt_of_not_ge hh
    have hp : 0<μ*‖g‖*(‖g‖-4*κ*‖projectedResidual s g‖) :=
      mul_pos (mul_pos hμ hgp) (sub_pos.mpr hlt)
    nlinarith only [ht,hp]

end
end krylov.Correction
