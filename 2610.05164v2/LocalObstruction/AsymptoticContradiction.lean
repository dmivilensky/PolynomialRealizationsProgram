import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Article: 2610.05164v2, Theorem 6.1.
The final contradiction in Theorem 6.1, isolated from the variational argument.
Use: `«2610.05164v2».LocalObstruction.no_stationary_identity` feeds
`«2610.05164v2».LocalObstruction.no_sine_stationary_identity` (no sine stationary identity).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Filter Asymptotics
open scoped Topology

/--
Exact identity `¬ ∀ᶠ x in atTop, (3/2:ℝ)*n x=α+ζ/(2*n x)+c₀+c₁*e x+n x*r x`.

Use: `«2610.05164v2».LocalObstruction.no_sine_stationary_identity` uses this identity to
establish exact identity `¬ ∀ᶠ x in atTop, (3/2:ℝ)*n x=α+ζ/(2*n x)+g x`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem no_stationary_identity {n e r : ℝ → ℝ} {c₀ c₁ α ζ : ℝ}
    (hn : ∀ᶠ x in atTop, 0 < n x)
    (hn₀ : Tendsto n atTop (𝓝 0)) (he₀ : Tendsto e atTop (𝓝 0))
    (hne : Tendsto (fun x => n x/e x) atTop (𝓝 0))
    (he : ∀ᶠ x in atTop, e x ≠ 0)
    (hr : Tendsto r atTop (𝓝 0)) :
    ¬ ∀ᶠ x in atTop,
      (3/2:ℝ)*n x=α+ζ/(2*n x)+c₀+c₁*e x+n x*r x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro hid
  have hζ : ζ=0 := by
    -- Record the convergence hl with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hl : Tendsto
        (fun x => n x*((3/2:ℝ)*n x-α-c₀-c₁*e x-n x*r x)) atTop (𝓝 0) := by
      convert hn₀.mul (((((hn₀.const_mul (3/2:ℝ)).sub_const α).sub_const c₀).sub
        (he₀.const_mul c₁)).sub (hn₀.mul hr)) using 1; simp
    have heq : (fun x => n x*((3/2:ℝ)*n x-α-c₀-c₁*e x-n x*r x))
        =ᶠ[atTop] fun _ => ζ/2 := by
      filter_upwards [hn,hid] with x hx hi
      have hnx := hx.ne'
      field_simp at hi ⊢
      nlinarith [hi]
    have hval := tendsto_nhds_unique hl (tendsto_const_nhds.congr' heq.symm)
    linarith
  have hac : α+c₀=0 := by
    -- Record the convergence hl with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hl : Tendsto (fun x => (3/2:ℝ)*n x-c₁*e x-n x*r x) atTop (𝓝 0) := by
      convert ((hn₀.const_mul (3/2:ℝ)).sub (he₀.const_mul c₁)).sub (hn₀.mul hr) using 1; simp
    have heq : (fun x => (3/2:ℝ)*n x-c₁*e x-n x*r x)=ᶠ[atTop] fun _ => α+c₀ := by
      filter_upwards [hid] with x hi
      simp only [hζ,zero_div,add_zero] at hi
      linarith
    exact (tendsto_nhds_unique hl (tendsto_const_nhds.congr' heq.symm)).symm
  have hc : c₁=0 := by
    -- Record the convergence hl with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hl : Tendsto (fun x => (3/2:ℝ)*(n x/e x)-(n x/e x)*r x)
        atTop (𝓝 0) := by
      convert (hne.const_mul (3/2:ℝ)).sub (hne.mul hr) using 1; simp
    have heq : (fun x => (3/2:ℝ)*(n x/e x)-(n x/e x)*r x)=ᶠ[atTop] fun _ => c₁ := by
      filter_upwards [hid,he] with x hi hx
      simp only [hζ,zero_div,add_zero] at hi
      have heq : (3/2:ℝ)*(n x/e x)-(n x/e x)*r x=
          ((3/2:ℝ)*n x-n x*r x)/e x := by ring
      rw [heq]
      apply (div_eq_iff hx).mpr
      linarith
    exact (tendsto_nhds_unique hl (tendsto_const_nhds.congr' heq.symm)).symm
  have heq : r=ᶠ[atTop] fun _ => (3/2:ℝ) := by
    filter_upwards [hid,hn] with x hi hx
    simp only [hζ,hc,zero_div,zero_mul,add_zero] at hi
    nlinarith [hac]
  have hlim := tendsto_nhds_unique hr (tendsto_const_nhds.congr' heq.symm)
  norm_num at hlim

end
end «2610.05164v2».LocalObstruction
