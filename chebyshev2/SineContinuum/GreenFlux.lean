import chebyshev2.SineContinuum.LegendreSymmetry
import chebyshev2.SineContinuum.ClosedProfiles

/-!
Article: chebyshev2, Proposition 2.
The apparent singular first derivatives cancel in the endpoint flux.
Use: `chebyshev2.SineContinuum.rightFlux_derivative` feeds
`chebyshev2.SineContinuum.rightFlux_integral` (right Flux integral).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `leftFlux` of type `(n : ℕ) (t : ℝ)` by `l₁ t*upsilon n t-l t*upsilon₁ n t`.

Use: `chebyshev2.SineContinuum.leftFlux_regular` rewrites with this definition to establish
exact identity `leftFlux n t=regularLeftFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def leftFlux (n : ℕ) (t : ℝ) := l₁ t*upsilon n t-l t*upsilon₁ n t
/--
Defines `rightFlux` of type `(n : ℕ) (t : ℝ)` by `r₁ t*upsilon n t-r t*upsilon₁ n t`.

Use: `chebyshev2.SineContinuum.rightFlux_reflect` uses this definition to establish exact
identity `rightFlux n t=-(-1:ℝ)^n*leftFlux n (1-t)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def rightFlux (n : ℕ) (t : ℝ) := r₁ t*upsilon n t-r t*upsilon₁ n t

/--
Continuity of the displayed function: `Continuous (upsilon n)`.

Use: `chebyshev2.SineContinuum.green_eigenfunction` uses this continuity result to
establish exact identity `(∫ s in (0:ℝ)..1, green t s*upsilon n s)=upsilon n t/mu n`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem upsilon_continuous (n : ℕ) : Continuous (upsilon n) := by
  unfold upsilon legendre chebyshev1.SineJacobi.profileWeight
  fun_prop

/--
The stated quantitative bound `0 < mu n`.

Use: `chebyshev2.SineContinuum.greenOperator_mem_domain` rewrites with this bound to
establish membership in the specified domain/enclosure: `greenOperator f ∈
sineOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.sineOperator_domain_eq_range`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mu_positive (n : ℕ) : 0 < mu n := by unfold mu; positivity

/--
Exact identity `l t=(2/π)*chebyshev1.SineJacobi.profileWeight t*
chebyshev1.SineJacobi.ellipticK (chebyshev1.SineJacobi.profileModulus t)`.

Use: `chebyshev2.SineContinuum.leftFlux_regular` rewrites with this identity to establish
exact identity `leftFlux n t=regularLeftFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem l_modulus_formula (t : ℝ) :
    l t=(2/π)*chebyshev1.SineJacobi.profileWeight t*
      chebyshev1.SineJacobi.ellipticK (chebyshev1.SineJacobi.profileModulus t) := by
  dsimp [l,chebyshev1.SineJacobi.sineProfile,chebyshev1.SineJacobi.profileWeight,chebyshev1.SineJacobi.profileModulus]
  field_simp [(sqrt_pos.mpr pi_pos).ne']

/--
Exact identity `l₁ t=(2/π)*(chebyshev1.SineJacobi.profileWeight₁ t*
chebyshev1.SineJacobi.ellipticK (chebyshev1.SineJacobi.profileModulus t)+
chebyshev1.SineJacobi.profileWeight t*chebyshev1.SineJacobi.ellipticK₁
(chebyshev1.SineJacobi.profileModulus t)*chebyshev1.SineJacobi.profileModulus₁ t)`.

Use: `chebyshev2.SineContinuum.leftFlux_regular` rewrites with this identity to establish
exact identity `leftFlux n t=regularLeftFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem l₁_modulus_formula (t : ℝ) :
    l₁ t=(2/π)*(chebyshev1.SineJacobi.profileWeight₁ t*
      chebyshev1.SineJacobi.ellipticK (chebyshev1.SineJacobi.profileModulus t)+
      chebyshev1.SineJacobi.profileWeight t*chebyshev1.SineJacobi.ellipticK₁
        (chebyshev1.SineJacobi.profileModulus t)*chebyshev1.SineJacobi.profileModulus₁ t) := by
  dsimp [l₁,chebyshev1.SineJacobi.sineProfile₁,chebyshev1.SineJacobi.profileElliptic,
    chebyshev1.SineJacobi.profileElliptic₁]
  field_simp [(sqrt_pos.mpr pi_pos).ne']

/--
The apparent singular first derivatives cancel in the endpoint flux.

Use: `chebyshev2.SineContinuum.leftFlux_regular` uses this definition to establish exact
identity `leftFlux n t=regularLeftFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def regularLeftFlux (n : ℕ) (t : ℝ) : ℝ :=
  (2/π)*√(π*((n:ℝ)+1/2))*sin (π*t)*
    (chebyshev1.SineJacobi.ellipticK₁ (chebyshev1.SineJacobi.profileModulus t)*
      chebyshev1.SineJacobi.profileModulus₁ t*legendre n (cos (π*t))-
      chebyshev1.SineJacobi.ellipticK (chebyshev1.SineJacobi.profileModulus t)*
        legendre₁ n (cos (π*t))*(-π*sin (π*t)))

/--
Exact identity `leftFlux n t=regularLeftFlux n t`.

Use: `chebyshev2.SineContinuum.leftFlux_zero_limit` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (leftFlux n)
(𝓝[>] (0:ℝ)) (𝓝 0)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.profileWeight_pos`,
`chebyshev2.SineContinuum.l_modulus_formula`,
`chebyshev2.SineContinuum.l₁_modulus_formula` with the arguments shown in the proof.
-/
theorem leftFlux_regular (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    leftFlux n t=regularLeftFlux n t := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.profileWeight_pos`,
  -- `chebyshev2.SineContinuum.l_modulus_formula`,
  -- `chebyshev2.SineContinuum.l₁_modulus_formula` with the arguments shown in the proof.
  have hw : chebyshev1.SineJacobi.profileWeight t^2=sin (π*t) :=
    sq_sqrt (sqrt_pos.mp (chebyshev1.SineJacobi.profileWeight_pos ht)).le
  rw [leftFlux,l_modulus_formula,l₁_modulus_formula]
  dsimp [upsilon,upsilon₁,regularLeftFlux]
  linear_combination (2/π)*√(π*((n:ℝ)+1/2))*
    (chebyshev1.SineJacobi.ellipticK₁ (chebyshev1.SineJacobi.profileModulus t)*
      chebyshev1.SineJacobi.profileModulus₁ t*legendre n (cos (π*t))-
      chebyshev1.SineJacobi.ellipticK (chebyshev1.SineJacobi.profileModulus t)*
        legendre₁ n (cos (π*t))*(-π*sin (π*t)))*hw

/--
Continuity at the stated point: `ContinuousAt (regularLeftFlux n) 0`.

Use: `chebyshev2.SineContinuum.leftFlux_zero_limit` uses this continuity result to
establish convergence along the specified source filter to the specified limit: `Tendsto
(leftFlux n) (𝓝[>] (0:ℝ)) (𝓝 0)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ellipticK_deriv`,
`chebyshev1.SineJacobi.profileModulus_deriv`, `chebyshev1.SineJacobi.ellipticK₁_deriv`
with the arguments shown in the proof.
-/
theorem regularLeftFlux_continuousAt_zero (n : ℕ) : ContinuousAt (regularLeftFlux n) 0 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.ellipticK_deriv`,
  -- `chebyshev1.SineJacobi.profileModulus_deriv`,
  -- `chebyshev1.SineJacobi.ellipticK₁_deriv` with the arguments shown in the proof.
  have hk : |chebyshev1.SineJacobi.profileModulus 0| < 1 := by
    simp [chebyshev1.SineJacobi.profileModulus]
  have hK := (chebyshev1.SineJacobi.ellipticK_deriv hk).continuousAt.comp
    (chebyshev1.SineJacobi.profileModulus_deriv 0).continuousAt
  have hK₁ := (chebyshev1.SineJacobi.ellipticK₁_deriv hk).continuousAt.comp
    (chebyshev1.SineJacobi.profileModulus_deriv 0).continuousAt
  -- Establish continuity hP before using the function at limits or in calculus arguments.
  have hP : ContinuousAt (fun t : ℝ => legendre n (cos (π*t))) 0 := (legendre_derivative n (cos (π*0))).continuousAt.comp (f := fun t : ℝ => cos (π*t)) (x := 0)
    (((hasDerivAt_id (0:ℝ)).const_mul π).cos).continuousAt
  -- Establish continuity hP₁ before using the function at limits or in calculus arguments.
  have hP₁ : ContinuousAt (fun t : ℝ => legendre₁ n (cos (π*t))) 0 := (legendre₁_derivative n (cos (π*0))).continuousAt.comp (f := fun t : ℝ => cos (π*t)) (x := 0)
    (((hasDerivAt_id (0:ℝ)).const_mul π).cos).continuousAt
  unfold regularLeftFlux
  exact ((continuousAt_const.mul continuousAt_const).mul
    (by fun_prop : ContinuousAt (fun t : ℝ => sin (π*t)) 0)).mul
      ((hK₁.mul (chebyshev1.SineJacobi.profileModulus₁_deriv 0).continuousAt).mul hP |>.sub
        ((hK.mul hP₁).mul (by fun_prop)))

/--
Convergence along the specified source filter to the specified limit: `Tendsto (leftFlux n)
(𝓝[>] (0:ℝ)) (𝓝 0)`.

Use: `chebyshev2.SineContinuum.rightFlux_one_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (rightFlux n)
(𝓝[<] (1:ℝ)) (𝓝 0)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem leftFlux_zero_limit (n : ℕ) : Tendsto (leftFlux n) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h : Tendsto (regularLeftFlux n) (𝓝[>] (0:ℝ)) (𝓝 (regularLeftFlux n 0)) :=
    (regularLeftFlux_continuousAt_zero n).tendsto.mono_left nhdsWithin_le_nhds
  rw [show regularLeftFlux n 0=0 by simp [regularLeftFlux]] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  exact (leftFlux_regular n ht).symm

/--
Exact identity `rightFlux n t=-(-1:ℝ)^n*leftFlux n (1-t)`.

Use: `chebyshev2.SineContinuum.rightFlux_one_limit` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (rightFlux n)
(𝓝[<] (1:ℝ)) (𝓝 0)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.upsilon_reflect`,
`chebyshev2.SineContinuum.upsilon₁_reflect` with the arguments shown in the proof.
-/
theorem rightFlux_reflect (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    rightFlux n t=-(-1:ℝ)^n*leftFlux n (1-t) := by
  have h0 : ((-1:ℝ)^n)^2=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  dsimp [leftFlux,rightFlux,r,r₁]
  rw [upsilon_reflect,upsilon₁_reflect n ht]
  linear_combination (l₁ (1-t)*upsilon n t+l (1-t)*upsilon₁ n t)*h0

/--
Convergence along the specified source filter to the specified limit: `Tendsto (rightFlux n)
(𝓝[<] (1:ℝ)) (𝓝 0)`.

Use: `chebyshev2.SineContinuum.rightFlux_integral` uses this limit to establish exact
identity `mu n*(∫ s in t..(1:ℝ), r s*upsilon n s)=-rightFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem rightFlux_one_limit (n : ℕ) : Tendsto (rightFlux n) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have h := ((leftFlux_zero_limit n).comp reflect_left).const_mul (-(-1:ℝ)^n)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with t ht
  exact (rightFlux_reflect n ht).symm

/--
The actual derivative at the stated point: `HasDerivAt (leftFlux n) (mu n*l t*upsilon n t) t`.

Use: `chebyshev2.SineContinuum.leftFlux_integral` uses this derivative formula to establish
exact identity `mu n*(∫ s in (0:ℝ)..t, l s*upsilon n s)=leftFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.l₁_derivative`,
`chebyshev2.SineContinuum.upsilon_derivative`, `chebyshev2.SineContinuum.l_derivative`
with the arguments shown in the proof.
-/
theorem leftFlux_derivative (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (leftFlux n) (mu n*l t*upsilon n t) t := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.l₁_derivative`,
  -- `chebyshev2.SineContinuum.upsilon_derivative`,
  -- `chebyshev2.SineContinuum.l_derivative` with the arguments shown in the proof.
  have hd := ((l₁_derivative ht).mul (upsilon_derivative n ht)).sub
    ((l_derivative ht).mul (upsilon₁_derivative n ht))
  convert hd using 1
  · rfl
  · have hl := l_ode ht
    have hu := upsilon_explicit_ode n ht
    linear_combination -upsilon n t*hl-l t*hu

/--
The actual derivative at the stated point: `HasDerivAt (rightFlux n) (mu n*r t*upsilon n t) t`.

Use: `chebyshev2.SineContinuum.rightFlux_integral` uses this derivative formula to
establish exact identity `mu n*(∫ s in t..(1:ℝ), r s*upsilon n s)=-rightFlux n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.r₁_derivative`,
`chebyshev2.SineContinuum.upsilon_derivative`, `chebyshev2.SineContinuum.r_derivative`
with the arguments shown in the proof.
-/
theorem rightFlux_derivative (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (rightFlux n) (mu n*r t*upsilon n t) t := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.r₁_derivative`,
  -- `chebyshev2.SineContinuum.upsilon_derivative`,
  -- `chebyshev2.SineContinuum.r_derivative` with the arguments shown in the proof.
  have hd := ((r₁_derivative ht).mul (upsilon_derivative n ht)).sub
    ((r_derivative ht).mul (upsilon₁_derivative n ht))
  convert hd using 1
  · rfl
  · have hr := r_ode ht
    have hu := upsilon_explicit_ode n ht
    linear_combination -upsilon n t*hr-r t*hu

end
end chebyshev2.SineContinuum
