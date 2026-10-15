import «2610.05164v2».SineContinuum.Wronskian

/-!
Article: 2610.05164v2, Proposition 2.
Definition 2's coordinate, with the explicit formula used in Proposition 2.
Use: `«2610.05164v2».SineContinuum.X_log_ratio` feeds `«2610.05164v2».SineContinuum.exp_twice_X`
(exp twice X).
Proof chain: `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue` — 2610.05164v2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false

/--
Definition 2's coordinate, with the explicit formula used in Proposition 2.

Use: `«2610.05164v2».SineContinuum.X_midpoint` rewrites with this definition to establish exact
identity `X (1/2)=0`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.
-/
def X (t : ℝ) : ℝ := (1/2)*(log (l t)-log (r t))

/--
The actual derivative at the stated point: `HasDerivAt X (SineJacobi.phi t)⁻¹ t`.

Use: `«2610.05164v2».SineContinuum.X_continuousOn` uses this derivative formula to establish
continuity on the stated domain: `ContinuousOn X (Ioo (0:ℝ) 1)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem X_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt X (SineJacobi.phi t)⁻¹ t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd := (((l_derivative ht).log (l_positive ht).ne').sub
    ((r_derivative ht).log (r_positive ht).ne')).const_mul (1/2:ℝ)
  convert hd using 1
  · funext u; rfl
  · rw [phi_product]
    field_simp [(l_positive ht).ne',(r_positive ht).ne']
    have hw := wronskian_eq_two ht
    dsimp [wronskian] at hw
    linear_combination -hw

/--
Continuity on the stated domain: `ContinuousOn X (Ioo (0:ℝ) 1)`.

Use: `«2610.05164v2».SineContinuum.X_strictMono` uses this continuity result to establish the
precise assertion is `StrictMonoOn X (Ioo (0:ℝ) 1)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_derivative` with the
arguments shown in the proof.
-/
theorem X_continuousOn : ContinuousOn X (Ioo (0:ℝ) 1) :=
  fun _ ht => (X_derivative ht).continuousAt.continuousWithinAt

/--
The precise assertion is `StrictMonoOn X (Ioo (0:ℝ) 1)`.

Use: `«2610.05164v2».SineContinuum.coordinate_integrable_iff` uses this assertion to establish
integrability of the displayed function: `Integrable g ↔ IntegrableOn (fun t => (SineJacobi.phi
t)⁻¹*g (X t)) (Ioo (0:ℝ) 1)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_continuousOn`,
`«2610.05164v2».SineContinuum.X_derivative`, `«2610.05164v2».SineJacobi.phi_pos` with the
arguments shown in the proof.
-/
theorem X_strictMono : StrictMonoOn X (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) 1) X_continuousOn
  intro t ht
  have hi : t ∈ Ioo (0:ℝ) 1 := interior_subset ht
  rw [(X_derivative hi).deriv]
  exact inv_pos.mpr (SineJacobi.phi_pos hi)

/--
Exact identity `X (1/2)=0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 2.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem X_midpoint : X (1/2)=0 := by simp only [X,r,show (1:ℝ)-1/2=1/2 by ring,sub_self,mul_zero]

/--
Exact identity `X (1-t)=-X t`.

Use: `«2610.05164v2».SineContinuum.T_reflect` rewrites with this identity to establish exact
identity `T (-x)=1-T x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem X_reflect (t : ℝ) : X (1-t)=-X t := by
  dsimp [X,r]
  rw [show 1-(1-t)=t by ring]
  ring

/--
Exact identity `X t=(1/2)*log (l t/r t)`.

Use: `«2610.05164v2».SineContinuum.exp_twice_X` rewrites with this identity to establish exact
identity `exp (2*X t)=l t/r t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_positive`,
`«2610.05164v2».SineContinuum.r_positive` with the arguments shown in the proof.
-/
theorem X_log_ratio {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : X t=(1/2)*log (l t/r t) := by
  rw [log_div (l_positive ht).ne' (r_positive ht).ne']
  rfl

end
end «2610.05164v2».SineContinuum
