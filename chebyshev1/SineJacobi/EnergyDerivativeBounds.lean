import chebyshev1.SineJacobi.ProfileDerivativeBounds
import chebyshev1.SineJacobi.EnergyBound

/-!
Article: chebyshev1, Theorem 5.2.
Explicit fourth-order control for the actual squared density.
Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` feeds
`chebyshev1.SineJacobi.gradedEnergy_fourth_bound` (The cubic grading has a uniform
fourth-derivative bound away from zero).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set chebyshev1.Analysis
set_option backward.isDefEq.respectTransparency false

/--
Defines `energyDensity` of type `ℝ` by `sineDensity t^2`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` rewrites with this
definition to prove the bound `WeightedDerivatives energyDensity t t
(fun n => energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def energyDensity (t : ℝ) : ℝ := sineDensity t^2

/--
Defines `productDerivativeBound` by pattern matching with result type `ℕ → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use:
`_private.chebyshev1.SineJacobi.EnergyDerivativeBounds.0.chebyshev1.SineJacobi.product_convolution`
uses this definition to establish the identity `(∑ i ∈ Finset.range (n+1), (n.choose i :
ℝ)*productDerivativeBound i* productDerivativeBound (n-i)) = energyDerivativeBound n`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def productDerivativeBound : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 16
  | _ => 128

/--
Defines `energyDerivativeBound` by pattern matching with result type `ℕ → ℝ`. The displayed
branches determine the recursive cases and their returned values.

Use:
`_private.chebyshev1.SineJacobi.EnergyDerivativeBounds.0.chebyshev1.SineJacobi.product_convolution`
uses this definition to establish the identity `(∑ i ∈ Finset.range (n+1), (n.choose i :
ℝ)*productDerivativeBound i* productDerivativeBound (n-i)) = energyDerivativeBound n`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.
-/
def energyDerivativeBound : ℕ → ℝ
  | 0 => 1
  | 1 => 4
  | 2 => 16
  | 3 => 80
  | _ => 608

/--
Exact identity `(∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*profileDerivativeBound i*
profileDerivativeBound (n-i)) = productDerivativeBound n`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` uses this identity to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem profile_convolution {n : ℕ} (hn : n ≤ 4) :
    (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*profileDerivativeBound i*
      profileDerivativeBound (n-i)) = productDerivativeBound n := by
  interval_cases n <;> norm_num [Nat.choose, Finset.sum_range_succ, profileDerivativeBound, productDerivativeBound]

/--
Exact identity `(∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*productDerivativeBound i*
productDerivativeBound (n-i)) = energyDerivativeBound n`.

Use: `chebyshev1.SineJacobi.energyDensity_weighted_derivatives` uses this identity to
establish the stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem product_convolution {n : ℕ} (hn : n ≤ 4) :
    (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*productDerivativeBound i*
      productDerivativeBound (n-i)) = energyDerivativeBound n := by
  interval_cases n <;> norm_num [Nat.choose, Finset.sum_range_succ, productDerivativeBound, energyDerivativeBound]

/--
Smoothness to the stated order: `ContDiffOn ℝ n sineDensity (Ioo (0:ℝ) 1)`.

Use: `chebyshev1.SineJacobi.energyDensity_contDiffOn` uses this assertion to establish
smoothness to the stated order: `ContDiffOn ℝ n energyDensity (Ioo (0:ℝ) 1)`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineProfile_contDiffOn` with the
arguments shown in the proof.
-/
theorem sineDensity_contDiffOn (n : ℕ) : ContDiffOn ℝ n sineDensity (Ioo (0:ℝ) 1) := by
  unfold sineDensity profileProduct
  apply ContDiffOn.mul contDiffOn_const
  apply (sineProfile_contDiffOn n).mul
  apply (sineProfile_contDiffOn n).comp (by fun_prop)
  intro x hx
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/--
Smoothness to the stated order: `ContDiffOn ℝ n energyDensity (Ioo (0:ℝ) 1)`.

Use:
`_private.chebyshev1.SineJacobi.GradedEnergy.0.chebyshev1.SineJacobi.gradedDerivative_deriv`
uses this assertion to establish the actual derivative at the stated point: `HasDerivAt
(gradedDerivative j) (gradedDerivative (j+1) s) s`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineDensity_contDiffOn` with the
arguments shown in the proof.
-/
theorem energyDensity_contDiffOn (n : ℕ) : ContDiffOn ℝ n energyDensity (Ioo (0:ℝ) 1) :=
  (sineDensity_contDiffOn n).pow 2

/--
Explicit fourth-order control for the actual squared density.

The stated quantitative bound `WeightedDerivatives energyDensity t t (fun n =>
energyDerivativeBound n*energyDensity t) 4`.

Use: `chebyshev1.SineJacobi.gradedEnergy_fourth_bound` uses this identity to establish the
stated quantitative bound `|iteratedDeriv 4 gradedEnergy s| ≤ 1300000`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem energyDensity_weighted_derivatives {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/2) :
    WeightedDerivatives energyDensity t t
      (fun n => energyDerivativeBound n*energyDensity t) 4 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have ht' : t ∈ Ioo (0:ℝ) 1 := ⟨ht, by linarith⟩
  have href : 1-t ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hq := profilePotential_weighted_bounds ht ht1
  have ha := sineProfile_weighted_derivatives ht' ht le_rfl (by linarith) hq.1 hq.2.1 hq.2.2
  have hq' := profilePotential_reflection t
  have hb' := sineProfile_weighted_derivatives href ht (by linarith) (by linarith)
    (by simpa only [hq'.1] using hq.1)
    (by simpa only [hq'.2.1, abs_neg] using hq.2.1)
    (by simpa only [hq'.2.2] using hq.2.2)
  have hb : WeightedDerivatives (fun x => sineProfile (1-x)) t t
      (fun n => profileDerivativeBound n*sineProfile (1-t)) 4 := by
    intro n hn
    simpa only [iteratedDeriv_comp_const_sub, smul_eq_mul, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul] using hb' n hn
  have hfa := (sineProfile_contDiffOn 4).contDiffAt (isOpen_Ioo.mem_nhds ht')
  have hfb : ContDiffAt ℝ 4 (fun x => sineProfile (1-x)) t :=
    ((sineProfile_contDiffOn 4).contDiffAt (isOpen_Ioo.mem_nhds href)).comp t (by fun_prop)
  have hprod : WeightedDerivatives profileProduct t t
      (fun n => productDerivativeBound n*profileProduct t) 4 := by
    intro n hn
    change |iteratedDeriv n (sineProfile * fun x => sineProfile (1-x)) t| * t^n ≤
      productDerivativeBound n*(sineProfile * fun x => sineProfile (1-x)) t
    simpa only [profile_convolution hn] using ha.mul_relative ht.le hfa hfb hb n hn
  have hden : WeightedDerivatives sineDensity t t
      (fun n => productDerivativeBound n*sineDensity t) 4 := by
    intro n hn
    change |iteratedDeriv n (fun x => Real.pi*profileProduct x) t| * t^n ≤
      productDerivativeBound n*(Real.pi*profileProduct t)
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos pi_pos]
    have hh := mul_le_mul_of_nonneg_left (hprod n hn) pi_pos.le
    convert hh using 1 <;> ring_nf
  have hfd := (sineDensity_contDiffOn 4).contDiffAt (isOpen_Ioo.mem_nhds ht')
  intro n hn
  have he : energyDensity = sineDensity*sineDensity := by
    funext x
    simp only [energyDensity, Pi.mul_apply, sq]
  rw [he]
  simpa only [product_convolution hn] using
    hden.mul_relative ht.le hfd hfd hden n hn

end
end chebyshev1.SineJacobi
