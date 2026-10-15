import «2610.05164v2».SineJacobi.Profile
import «2606.16671v2».SineJacobi.ProfileODE

/-!
Article: 2610.05164v2, Lemma 5.
Lemma 5's left zero-energy solution, reusing the proved 2606.16671v2 profile.
Use: `«2610.05164v2».SineContinuum.l_boundary` feeds `«2610.05164v2».SineContinuum.l_left_limit` (l
left limit).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Lemma 5's left zero-energy solution, reusing the proved 2606.16671v2 profile.

Use: `«2610.05164v2».SineContinuum.green` uses this definition in the displayed construction of
`green`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.
-/
def l (t : ℝ) : ℝ := sqrt π*«2606.16671v2».SineJacobi.sineProfile t
/--
Defines `l₁` of type `ℝ` by `sqrt π*«2606.16671v2».SineJacobi.sineProfile₁ t`.

Use: `«2610.05164v2».SineContinuum.r₁` uses this definition in the displayed construction of
`r₁`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.
-/
def l₁ (t : ℝ) : ℝ := sqrt π*«2606.16671v2».SineJacobi.sineProfile₁ t
/--
Defines `l₂` of type `ℝ` by `sqrt π*«2606.16671v2».SineJacobi.sineProfile₂ t`.

Use: `«2610.05164v2».SineContinuum.l_ode` uses this definition to establish the identity `l₂
t+potential t*l t=0`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.
-/
def l₂ (t : ℝ) : ℝ := sqrt π*«2606.16671v2».SineJacobi.sineProfile₂ t
/--
Defines `r` of type `ℝ` by `l (1-t)`.

Use: `«2610.05164v2».SineContinuum.green` uses this definition in the displayed construction of
`green`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.
-/
def r (t : ℝ) : ℝ := l (1-t)
/--
Defines `r₁` of type `ℝ` by `-l₁ (1-t)`.

Use: `«2610.05164v2».SineContinuum.r_derivative` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt r (r₁ t) t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.
-/
def r₁ (t : ℝ) : ℝ := -l₁ (1-t)
/--
Defines `r₂` of type `ℝ` by `l₂ (1-t)`.

Use: `«2610.05164v2».SineContinuum.r₁_derivative` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt r₁ (r₂ t) t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.
-/
def r₂ (t : ℝ) : ℝ := l₂ (1-t)
/--
Defines `potential` of type `ℝ` by `π^2/(4*sin (π*t)^2)`.

Use: `«2610.05164v2».SineContinuum.l_ode` uses this definition to establish the identity `l₂
t+potential t*l t=0`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.
-/
def potential (t : ℝ) : ℝ := π^2/(4*sin (π*t)^2)
/--
Defines `wronskian` of type `ℝ` by `l₁ t*r t-l t*r₁ t`.

Use: `«2610.05164v2».SineContinuum.wronskian_constant` uses this definition to establish exact
identity `wronskian t=wronskian (1/2)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.
-/
def wronskian (t : ℝ) : ℝ := l₁ t*r t-l t*r₁ t
/--
Defines `green` of type `ℝ` by `(1/2)*l (min t s)*r (max t s)`.

Use: `«2610.05164v2».SineContinuum.green_diagonal` rewrites with this definition to establish
exact identity `2*green t t=SineJacobi.phi t`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.
-/
def green (t s : ℝ) : ℝ := (1/2)*l (min t s)*r (max t s)

/--
Membership in the specified domain/enclosure: `1-t ∈ Ioo (0:ℝ) 1`.

Use: `«2610.05164v2».SineContinuum.r_derivative` uses this assertion to establish the actual
derivative at the stated point: `HasDerivAt r (r₁ t) t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem reflect_mem {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 1-t ∈ Ioo (0:ℝ) 1 :=
  ⟨by linarith [ht.2],by linarith [ht.1]⟩

/--
Exact identity `l t=(2/π)*sqrt (sin (π*t))*SineJacobi.ellipticK (sin (π*t/2)^2)`.

Use: `«2610.05164v2».SineContinuum.l_midpoint` rewrites with this identity to establish exact
identity `l (1/2)=(2/π)*ellipticK (sqrt 2/2)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem l_formula (t : ℝ) :
    l t=(2/π)*sqrt (sin (π*t))*SineJacobi.ellipticK (sin (π*t/2)^2) := by
  rw [SineJacobi.ellipticK_square]
  dsimp [l,«2606.16671v2».SineJacobi.sineProfile]
  field_simp [(sqrt_pos.mpr pi_pos).ne']

/--
The stated quantitative bound `0 < l t`.

Use: `«2610.05164v2».SineContinuum.r_positive` uses this bound to establish the stated
quantitative bound `0 < r t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile_pos` with the
arguments shown in the proof.
-/
theorem l_positive {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 < l t :=
  mul_pos (sqrt_pos.mpr pi_pos) («2606.16671v2».SineJacobi.sineProfile_pos ht)
/--
The stated quantitative bound `0 < r t`.

Use: `«2610.05164v2».SineContinuum.X_derivative` uses this bound to establish the actual
derivative at the stated point: `HasDerivAt X (SineJacobi.phi t)⁻¹ t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_positive`,
`«2610.05164v2».SineContinuum.reflect_mem` with the arguments shown in the proof.
-/
theorem r_positive {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 < r t := l_positive (reflect_mem ht)

/--
The actual derivative at the stated point: `HasDerivAt l (l₁ t) t`.

Use: `«2610.05164v2».SineContinuum.r_derivative` uses this derivative formula to establish the
actual derivative at the stated point: `HasDerivAt r (r₁ t) t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile_deriv` with the
arguments shown in the proof.
-/
theorem l_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt l (l₁ t) t :=
  («2606.16671v2».SineJacobi.sineProfile_deriv ht).const_mul _
/--
The actual derivative at the stated point: `HasDerivAt l₁ (l₂ t) t`.

Use: `«2610.05164v2».SineContinuum.r₁_derivative` uses this derivative formula to establish the
actual derivative at the stated point: `HasDerivAt r₁ (r₂ t) t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile₁_deriv` with the
arguments shown in the proof.
-/
theorem l₁_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt l₁ (l₂ t) t :=
  («2606.16671v2».SineJacobi.sineProfile₁_deriv ht).const_mul _

/--
The actual derivative at the stated point: `HasDerivAt r (r₁ t) t`.

Use: `«2610.05164v2».SineContinuum.wronskian_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt wronskian 0 t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem r_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt r (r₁ t) t := by
  have hd := (l_derivative (reflect_mem ht)).comp t ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))
  convert hd using 1
  · funext u; rfl
  · dsimp [r₁]; ring

/--
The actual derivative at the stated point: `HasDerivAt r₁ (r₂ t) t`.

Use: `«2610.05164v2».SineContinuum.wronskian_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt wronskian 0 t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem r₁_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt r₁ (r₂ t) t := by
  have hd := ((l₁_derivative (reflect_mem ht)).comp t
    ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))).neg
  convert hd using 1
  · funext u; rfl
  · dsimp [r₂]; ring

/--
Exact identity `l₂ t+potential t*l t=0`.

Use: `«2610.05164v2».SineContinuum.r_ode` uses this identity to establish the identity `r₂
t+potential t*r t=0`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile_explicit_ode` with
the arguments shown in the proof.
-/
theorem l_ode {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : l₂ t+potential t*l t=0 := by
  have hd := «2606.16671v2».SineJacobi.sineProfile_explicit_ode ht
  dsimp [l₂,potential,l]
  linear_combination sqrt π*hd

/--
Exact identity `potential (1-t)=potential t`.

Use: `«2610.05164v2».SineContinuum.r_ode` rewrites with this identity to establish exact
identity `r₂ t+potential t*r t=0`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem potential_reflect (t : ℝ) : potential (1-t)=potential t := by
  dsimp [potential]
  rw [show π*(1-t)=π-π*t by ring,sin_pi_sub]

/--
Exact identity `r₂ t+potential t*r t=0`.

Use: `«2610.05164v2».SineContinuum.wronskian_derivative` uses this identity to establish the
actual derivative at the stated point: `HasDerivAt wronskian 0 t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_ode`,
`«2610.05164v2».SineContinuum.reflect_mem`, `«2610.05164v2».SineContinuum.potential_reflect`
with the arguments shown in the proof.
-/
theorem r_ode {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : r₂ t+potential t*r t=0 := by
  have hd := l_ode (reflect_mem ht)
  rw [potential_reflect] at hd
  exact hd

/--
The actual derivative at the stated point: `HasDerivAt wronskian 0 t`.

Use: `«2610.05164v2».SineContinuum.wronskian_constant` uses this derivative formula to
establish exact identity `wronskian t=wronskian (1/2)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l₁_derivative`,
`«2610.05164v2».SineContinuum.r_derivative`, `«2610.05164v2».SineContinuum.l_derivative` with
the arguments shown in the proof.
-/
theorem wronskian_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt wronskian 0 t := by
  have hd := ((l₁_derivative ht).mul (r_derivative ht)).sub
    ((l_derivative ht).mul (r₁_derivative ht))
  convert hd using 1
  · rfl
  · linear_combination -r t*l_ode ht+l t*r_ode ht

/--
Exact identity `wronskian t=wronskian (1/2)`.

Use: `«2610.05164v2».SineContinuum.wronskian_eq_two` rewrites with this identity to establish
exact identity `wronskian t=2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: A vanishing derivative makes the relevant function constant on the connected interval.
-/
theorem wronskian_constant {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    wronskian t=wronskian (1/2) := by
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (wronskian_derivative ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (wronskian_derivative ht).deriv)
  exact (hc t ht).trans (hc (1/2) (by norm_num)).symm

/--
Exact identity `SineJacobi.phi t=l t*r t`.

Use: `«2610.05164v2».SineContinuum.green_diagonal` rewrites with this identity to establish
exact identity `2*green t t=SineJacobi.phi t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem phi_product (t : ℝ) : SineJacobi.phi t=l t*r t := by
  dsimp [SineJacobi.phi,«2606.16671v2».SineJacobi.sineDensity,«2606.16671v2».SineJacobi.profileProduct,l,r]
  linear_combination -(«2606.16671v2».SineJacobi.sineProfile t*«2606.16671v2».SineJacobi.sineProfile (1-t))*
    (sq_sqrt pi_pos.le)

/--
Exact identity `2*green t t=SineJacobi.phi t`.

Use: `«2610.05164v2».SineContinuum.green_diagonal_integral` uses this identity to establish
exact identity `(∫ t in (0:ℝ)..1, green t t)=1/2`.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.phi_product` with the
arguments shown in the proof.
-/
theorem green_diagonal (t : ℝ) : 2*green t t=SineJacobi.phi t := by
  rw [phi_product]
  simp only [green,min_self,max_self]
  ring

/--
Exact identity `green t s=green s t`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem green_symmetric (t s : ℝ) : green t s=green s t := by simp only [green,min_comm,max_comm]

/--
Exact identity `SineJacobi.phi (1-t)=SineJacobi.phi t`.

Use: `«2610.05164v2».SineContinuum.n_even` rewrites with this identity to establish exact
identity `n (-x)=n x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.phi_product` with the
arguments shown in the proof.
-/
theorem phi_reflect (t : ℝ) : SineJacobi.phi (1-t)=SineJacobi.phi t := by
  rw [phi_product,phi_product]
  simp only [r,show 1-(1-t)=t by ring,mul_comm]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun t => l
t/sqrt t) (𝓝[>] (0:ℝ)) (𝓝 (sqrt π))`.

Use: `«2610.05164v2».SineContinuum.l_left_limit` uses this limit to establish convergence along
the specified source filter to the specified limit: `Tendsto l (𝓝[>] (0:ℝ)) (𝓝 0)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile_boundary` with the
arguments shown in the proof.
-/
theorem l_boundary : Tendsto (fun t => l t/sqrt t) (𝓝[>] (0:ℝ)) (𝓝 (sqrt π)) := by
  have hd := (tendsto_const_nhds (x := sqrt π)).mul «2606.16671v2».SineJacobi.sineProfile_boundary
  simpa only [mul_one,l,mul_div_assoc] using hd

end
end «2610.05164v2».SineContinuum
