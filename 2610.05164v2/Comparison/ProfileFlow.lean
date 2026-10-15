import «2610.05164v2».Comparison.ProfileIntegrability

/-!
Article: 2610.05164v2, Theorem 3.4.
The interior comparison flow for every Definition 10 profile.
Use: `«2610.05164v2».Comparison.Profile.determinantPotential_flow_derivative` feeds
`«2610.05164v2».Comparison.Profile.determinantAlong_derivative` (determinant Along derivative).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
section Static
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ) (hκ : 0 < κ)

/--
The actual derivative at the stated point: `HasDerivAt (fun t => P.determinantPotential hκ s (q
t) (r t)) (-(r x*P.rightFilter hκ s (q x)+s*(P.amplitude (q x))^2)/ (P.speed (q x)*(2+r
x+P.rightFilter hκ s (q x)))*u+ v/(2+r x+P.rightFilter hκ s (q x))) x`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_flow_derivative` uses this
derivative formula to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinantPotential_path_derivative {s x u v : ℝ} {q r : ℝ → ℝ}
    (hs : 0 ≤ s) (hq : q x ∈ Ioo (0:ℝ) 2) (hr : 0 ≤ r x)
    (hdq : HasDerivAt q u x) (hdr : HasDerivAt r v x) :
    HasDerivAt (fun t => P.determinantPotential hκ s (q t) (r t))
      (-(r x*P.rightFilter hκ s (q x)+s*(P.amplitude (q x))^2)/
        (P.speed (q x)*(2+r x+P.rightFilter hκ s (q x)))*u+
        v/(2+r x+P.rightFilter hκ s (q x))) x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hR := P.rightFilter_bounds hκ hs ⟨hq.1.le,hq.2.le⟩
  have hn : 2+r x+P.rightFilter hκ s (q x) ≠ 0 := ne_of_gt (by linarith [hR.1])
  have h := ((P.determinantL_derivative hκ hs hq).comp x hdq).add
    ((((hasDerivAt_const x (2:ℝ)).add hdr).add
      ((P.rightFilter_derivative hκ hs hq).comp x hdq)).div_const 2 |>.log
        (div_ne_zero hn (by norm_num)))
  convert h using 1
  · rfl
  · simp only [Pi.add_apply,Function.comp_apply]
    field_simp [(P.speed_pos hq).ne',hn]
    ring

end Static
section Along
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
  (P : «2610.05164v2».Comparison.Profile (groundParameter hm hn))

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, G.q x ∈ Ioo (0:ℝ) 2 →
HasDerivAt (fun t => P.determinantPotential G.coupling_positive s (G.q t) (nonlinear s m t))
(-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)* (m
x-(P.amplitude (G.q x))^2)) x`.

Use: `«2610.05164v2».Comparison.Profile.determinantAlong_derivative` uses this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(determinantAlong G P (s := s)) (-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x)
(nonlinear s m x)* (m x-(P.amplitude (G.q x))^2)) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem determinantPotential_flow_derivative {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ x, G.q x ∈ Ioo (0:ℝ) 2 → HasDerivAt
      (fun t => P.determinantPotential G.coupling_positive s (G.q t) (nonlinear s m t))
      (-nonlinear s m x+P.comparisonA G.coupling_positive s (G.q x) (nonlinear s m x)*
        (m x-(P.amplitude (G.q x))^2)) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [G.coordinate_derivative,nonlinear_derivative hm hn hs] with x hq hr hx
  have hp := P.determinantPotential_path_derivative G.coupling_positive hs hx
    (nonlinear_bounds hm hn hs x).1 hq hr
  convert hp using 1
  have hR := P.rightFilter_bounds G.coupling_positive hs ⟨hx.1.le,hx.2.le⟩
  have hden : 2+nonlinear s m x+P.rightFilter G.coupling_positive s (G.q x) ≠ 0 :=
    ne_of_gt (by linarith [(nonlinear_bounds hm hn hs x).1,hR.1])
  rw [comparisonA,ite_eq_left hx]
  unfold determinantCoefficient
  field_simp [(P.speed_pos hx).ne',hden]
  rw [P.speed_eq ⟨hx.1.le,hx.2.le⟩]
  unfold «2610.05164v2».Calibration.Q
  ring

end Along
end
end «2610.05164v2».Comparison.Profile
