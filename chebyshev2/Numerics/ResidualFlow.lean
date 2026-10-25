import chebyshev2.Numerics.RiccatiFlow

/-!
Article: chebyshev2, Section 4.1.
A posteriori verification of polynomial approximations of dissipative scalar ODEs.
Use: `chebyshev2.Numerics.riccati_residual_bound_nonnegative` feeds
`chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.error` (error).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set Real
set_option autoImplicit false

/--
The stated quantitative bound `e t ≤ r + η * (t-a)`.

Use: `chebyshev2.Numerics.dissipative_linear_residual` uses this bound to establish the
stated quantitative bound `|e t| ≤ r + η * (t-a)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem dissipative_upper {e q d : ℝ → ℝ} {a b r η : ℝ}
    (he : ContinuousOn e (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt e (q t * e t + d t) (Ici t) t)
    (hq : ∀ t ∈ Ico a b, q t ≤ 0) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (h0 : e a ≤ r) (hres : ∀ t ∈ Ico a b, d t ≤ η)
    {t : ℝ} (ht : t ∈ Icc a b) : e t ≤ r + η * (t-a) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have H : ∀ ε ∈ Ioi (0 : ℝ), e t ≤ r + (η+ε) * (t-a) := by
    intro ε hε
    change 0 < ε at hε
    apply image_le_of_deriv_right_lt_deriv_boundary he hd
      (B := fun x => r + (η+ε) * (x-a)) (B' := fun _ => η+ε)
    · simpa using h0
    · intro x
      convert (((hasDerivAt_id x).sub_const a).const_mul (η+ε)).const_add r using 1 <;> simp
    · intro x hx hxB
      have hp : 0 ≤ e x := by
        rw [hxB]
        exact add_nonneg hr (mul_nonneg (add_nonneg hη hε.le) (sub_nonneg.mpr hx.1))
      have hmul := mul_nonpos_of_nonpos_of_nonneg (hq x hx) hp
      linarith [hres x hx]
    · exact ht
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousWithinAt (fun ε : ℝ => r + (η+ε) * (t-a)) (Ioi 0) 0 := by
    fun_prop
  have hh := continuousWithinAt_const.closure_le
    (show (0 : ℝ) ∈ closure (Ioi 0) by simp) hc H
  simpa using hh

/--
The stated quantitative bound `|e t| ≤ r + η * (t-a)`.

Use: `chebyshev2.Numerics.riccati_residual_bound` uses this bound to establish the stated
quantitative bound `|y t - p t| ≤ r + η * (t-a)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`_private.chebyshev2.Numerics.ResidualFlow.0.chebyshev2.Numerics.dissipative_upper`
with the arguments shown in the proof.
-/
theorem dissipative_linear_residual {e q d : ℝ → ℝ} {a b r η : ℝ}
    (he : ContinuousOn e (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt e (q t * e t + d t) (Ici t) t)
    (hq : ∀ t ∈ Ico a b, q t ≤ 0) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (h0 : |e a| ≤ r) (hres : ∀ t ∈ Ico a b, |d t| ≤ η)
    {t : ℝ} (ht : t ∈ Icc a b) : |e t| ≤ r + η * (t-a) := by
  -- Apply
  -- `_private.chebyshev2.Numerics.ResidualFlow.0.chebyshev2.Numerics.dissipative_upper`
  -- to the displayed hypotheses, then match the resulting expression to the goal.
  have hu := dissipative_upper he hd hq hr hη (le_abs_self _ |>.trans h0)
    (fun x hx => (le_abs_self _).trans (hres x hx)) ht
  have hl := dissipative_upper (e := fun x => -e x) (q := q) (d := fun x => -d x)
    he.neg (fun x hx => by convert (hd x hx).neg using 1; ring) hq hr hη
    (neg_le_abs _ |>.trans h0) (fun x hx => (neg_le_abs _).trans (hres x hx)) ht
  exact abs_le.mpr ⟨by linarith, hu⟩

/--
The stated quantitative bound `|y t - p t| ≤ r + η * (t-a)`.

Use: `chebyshev2.Numerics.riccati_residual_bound_nonnegative` uses this bound to establish
the stated quantitative bound `|y t - p t| ≤ r + η * (t-a)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.dissipative_linear_residual` with
the arguments shown in the proof.
-/
theorem riccati_residual_bound {C A B y p p' : ℝ → ℝ} {a b r η : ℝ}
    (hy : ContinuousOn y (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hyd : ∀ t ∈ Ico a b,
      HasDerivWithinAt y (C t + A t * y t + B t * y t^2) (Ici t) t)
    (hpd : ∀ t ∈ Ico a b, HasDerivWithinAt p (p' t) (Ici t) t)
    (hslope : ∀ t ∈ Ico a b, A t + B t * (y t + p t) ≤ 0)
    (hr : 0 ≤ r) (hη : 0 ≤ η) (h0 : |y a - p a| ≤ r)
    (hres : ∀ t ∈ Ico a b, |C t + A t * p t + B t * p t^2 - p' t| ≤ η)
    {t : ℝ} (ht : t ∈ Icc a b) : |y t - p t| ≤ r + η * (t-a) := by
  -- Use the identities/estimates `chebyshev2.Numerics.dissipative_linear_residual` with
  -- the arguments shown in the proof.
  apply dissipative_linear_residual (e := fun x => y x - p x)
    (q := fun x => A x + B x * (y x + p x))
    (d := fun x => C x + A x * p x + B x * p x^2 - p' x)
    (hy.sub hp) _ hslope hr hη h0 hres ht
  intro x hx
  convert (hyd x hx).sub (hpd x hx) using 1
  ring

/--
Nonnegative solutions and approximants suffice for the common stable filter case; no numerical
tube for the actual solution is assumed.

The stated quantitative bound `|y t - p t| ≤ r + η * (t-a)`.

Use: `chebyshev2.Numerics.IntegerCertificate.ResidualCell.Row.error` uses this bound to
establish the stated quantitative bound `|y t-r.approx s t|≤e+(η:ℝ)*(t-r.left s)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Numerics.riccati_residual_bound` with the
arguments shown in the proof.
-/
theorem riccati_residual_bound_nonnegative {C A B y p p' : ℝ → ℝ} {a b r η : ℝ}
    (hy : ContinuousOn y (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hyd : ∀ t ∈ Ico a b,
      HasDerivWithinAt y (C t + A t * y t + B t * y t^2) (Ici t) t)
    (hpd : ∀ t ∈ Ico a b, HasDerivWithinAt p (p' t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, A t ≤ 0) (hB : ∀ t ∈ Ico a b, B t ≤ 0)
    (hy0 : ∀ t ∈ Ico a b, 0 ≤ y t) (hp0 : ∀ t ∈ Ico a b, 0 ≤ p t)
    (hr : 0 ≤ r) (hη : 0 ≤ η) (h0 : |y a - p a| ≤ r)
    (hres : ∀ t ∈ Ico a b, |C t + A t * p t + B t * p t^2 - p' t| ≤ η)
    {t : ℝ} (ht : t ∈ Icc a b) : |y t - p t| ≤ r + η * (t-a) :=
  riccati_residual_bound hy hp hyd hpd
    (fun x hx => add_nonpos (hA x hx)
      (mul_nonpos_of_nonpos_of_nonneg (hB x hx) (add_nonneg (hy0 x hx) (hp0 x hx))))
    hr hη h0 hres ht

end
end chebyshev2.Numerics
