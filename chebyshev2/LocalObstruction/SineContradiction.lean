import chebyshev2.LocalObstruction.AsymptoticContradiction
import chebyshev2.LocalObstruction.SineDecay

/-!
Article: chebyshev2, Theorem 6.1.
The last step of Theorem 6.1 for the actual sine density.
Use: `chebyshev2.LocalObstruction.no_sine_stationary_identity` feeds
`chebyshev2.LocalObstruction.sine_nonstationary_test` (sine nonstationary test).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Real Filter Asymptotics chebyshev2.SineContinuum
open scoped Topology

/--
Exact identity `¬ ∀ᶠ x in atTop, (3/2:ℝ)*n x=α+ζ/(2*n x)+g x`.

Use: `chebyshev2.LocalObstruction.sine_nonstationary_test` uses this identity to establish
constructs witnesses with the exact properties `∃ v : SmoothTest, (∫ x, v x)=0 ∧ (∫ x, v x/(2*n
x))=0 ∧ (∫ x, v x*((3/2:ℝ)*n x-g x))≠0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem no_sine_stationary_identity {g : ℝ → ℝ} {c₀ c₁ α ζ : ℝ}
    (hg : (fun x => g x-c₀-c₁*exp (-2*x)) =o[atTop] n) :
    ¬ ∀ᶠ x in atTop, (3/2:ℝ)*n x=α+ζ/(2*n x)+g x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro hid
  -- Record the convergence hex with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hex : Tendsto (fun x : ℝ => exp (-2*x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2)))
  apply no_stationary_identity (n := n) (e := fun x => exp (-2*x))
    (r := fun x => (g x-c₀-c₁*exp (-2*x))/n x)
    (c₀ := c₀) (c₁ := c₁) (α := α) (ζ := ζ)
    (Eventually.of_forall n_positive) sine_amplitude_tendsto_zero
    hex
    sine_amplitude_div_exponential (Eventually.of_forall (fun x => exp_ne_zero _))
    hg.tendsto_div_nhds_zero
  filter_upwards [hid] with x hx
  have hnx := (n_positive x).ne'
  rw [mul_div_cancel₀ _ hnx]
  linarith

end
end chebyshev2.LocalObstruction
