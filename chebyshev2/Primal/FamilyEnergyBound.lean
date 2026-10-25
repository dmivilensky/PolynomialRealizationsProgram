import chebyshev2.Primal.FamilyMomentVariation
import chebyshev2.Primal.EnergyStability
import Mathlib.Topology.ContinuousMap.Compact

/-!
Article: chebyshev2, Proposition 13.
Proposition 13's energy bound for an arbitrary finite family, with the actual uniform norms of its
directions on the unit interval.
Use: `chebyshev2.Primal.affine_family_energy_bound` feeds `chebyshev2.Primal.proposition_13`
(Proposition 13, for continuous directions and hence for all polynomial families).
Proof chain: `chebyshev2.Primal.exact_primal_family_of_contraction` — chebyshev2, Theorem 5.2;
Contraction implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/--
Defines `unitDirection` of type `C(Icc (0:ℝ) 1,ℝ)` by `⟨fun t => θ t,hθ.comp
continuous_subtype_val⟩`.

Use: `chebyshev2.Primal.direction_norm_bound` uses this definition to establish the stated
quantitative bound `|θ t|≤‖unitDirection hθ‖`.

Article: chebyshev2, Theorem 5.2 via
`chebyshev2.Primal.exact_primal_family_of_contraction`.
-/
def unitDirection {θ : ℝ → ℝ} (hθ : Continuous θ) : C(Icc (0:ℝ) 1,ℝ) :=
  ⟨fun t => θ t,hθ.comp continuous_subtype_val⟩

/--
The stated quantitative bound `|θ t|≤‖unitDirection hθ‖`.

Use: `chebyshev2.Primal.affine_profile_difference_bound` uses this bound to establish the
stated quantitative bound `|affineProfile ψ θ a t-affineProfile ψ θ b t|≤‖a-b‖*∑
i,‖unitDirection (hθ i)‖`.

Article: chebyshev2, Theorem 5.2 via
`chebyshev2.Primal.exact_primal_family_of_contraction`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem direction_norm_bound {θ : ℝ → ℝ} (hθ : Continuous θ) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) : |θ t|≤‖unitDirection hθ‖ := by
  simpa only [Real.norm_eq_abs,unitDirection,ContinuousMap.coe_mk] using
    (unitDirection hθ).norm_coe_le_norm ⟨t,ht⟩

/--
The stated quantitative bound `|affineProfile ψ θ a t-affineProfile ψ θ b t|≤‖a-b‖*∑
i,‖unitDirection (hθ i)‖`.

Use: `chebyshev2.Primal.affine_family_energy_bound` uses this bound to establish the stated
quantitative bound `(∫ x,(speedData (affineProfile ψ θ a) (affineProfile_continuous hψ hθ
a)).density κ x^(3/2:ℝ))≤ exp (‖a‖*∑ i,‖unitDirection (hθ i)‖)* (∫ x,(speedData ψ hψ).density κ
x^(3/2:ℝ))`.

Article: chebyshev2, Theorem 5.2 via
`chebyshev2.Primal.exact_primal_family_of_contraction`.

Proof: Use the identities/estimates `chebyshev2.Primal.direction_norm_bound` with the
arguments shown in the proof.
-/
theorem affine_profile_difference_bound (ψ : ℝ → ℝ) {θ : ι → ℝ → ℝ}
    (hθ : ∀ i,Continuous (θ i)) (a b : ι → ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |affineProfile ψ θ a t-affineProfile ψ θ b t|≤‖a-b‖*∑ i,‖unitDirection (hθ i)‖ := by
  -- Use the identities/estimates `chebyshev2.Primal.direction_norm_bound` with the
  -- arguments shown in the proof.
  have he : affineProfile ψ θ a t-affineProfile ψ θ b t=∑ i,(a i-b i)*θ i t := by
    unfold affineProfile
    simp_rw [sub_mul,Finset.sum_sub_distrib]
    ring
  rw [he,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (a-b) i)
    (direction_norm_bound (hθ i) ht) (abs_nonneg _) (norm_nonneg _)

/--
The stated quantitative bound `(∫ x,(speedData (affineProfile ψ θ a) (affineProfile_continuous
hψ hθ a)).density κ x^(3/2:ℝ))≤ exp (‖a‖*∑ i,‖unitDirection (hθ i)‖)* (∫ x,(speedData ψ
hψ).density κ x^(3/2:ℝ))`.

Use: `chebyshev2.Primal.exact_primal_family_of_contraction` uses this bound to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 5.2 via
`chebyshev2.Primal.exact_primal_family_of_contraction`.

Proof: Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
`chebyshev2.Primal.density_energy_stability`,
`chebyshev2.Primal.affine_profile_difference_bound` with the arguments shown in the proof.
-/
theorem affine_family_energy_bound {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ) (a : ι → ℝ) :
    (∫ x,(speedData (affineProfile ψ θ a) (affineProfile_continuous hψ hθ a)).density κ x^(3/2:ℝ))≤
      exp (‖a‖*∑ i,‖unitDirection (hθ i)‖)*
        (∫ x,(speedData ψ hψ).density κ x^(3/2:ℝ)) := by
  -- Use the identities/estimates `chebyshev2.Primal.affineProfile_continuous`,
  -- `chebyshev2.Primal.density_energy_stability`,
  -- `chebyshev2.Primal.affine_profile_difference_bound` with the arguments shown in the
  -- proof.
  apply density_energy_stability (affineProfile_continuous hψ hθ a) hψ hκ
  intro t ht
  have h := affine_profile_difference_bound ψ hθ a 0 ht
  simpa only [affineProfile,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,sub_zero] using h

end
end chebyshev2.Primal
