import chebyshev2.SineContinuum.EllipticSecond
import chebyshev1.SineJacobi.EllipticDescent

/-!
Article: chebyshev2, Proposition 2.
Legendre's complementary elliptic-integral identity, with its exact constant obtained from genuine
integral endpoint limits.
Use: `chebyshev2.SineContinuum.ellipticLegendre_identity` feeds
`chebyshev2.SineContinuum.wronskian_eq_two` (Lemma 5's exact Wronskian constant, derived from
the complementary elliptic identity with its independently proved endpoint normalization).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open chebyshev1.SineJacobi Set Real MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `complementary` of type `ℝ` by `sqrt (1-k^2)`.

Use: `chebyshev2.SineContinuum.complementary_K_bound` uses this definition to establish the
stated quantitative bound `k*ellipticK (complementary k) ≤ π/2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def complementary (k : ℝ) : ℝ := sqrt (1-k^2)
/--
Defines `ellipticLegendre` of type `ℝ` by `ellipticE k*ellipticK (complementary k)+ellipticK
k*ellipticE (complementary k)- ellipticK k*ellipticK (complementary k)`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto ellipticLegendre
(𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def ellipticLegendre (k : ℝ) : ℝ :=
  ellipticE k*ellipticK (complementary k)+ellipticK k*ellipticE (complementary k)-
    ellipticK k*ellipticK (complementary k)

/--
Membership in the specified domain/enclosure: `complementary k ∈ Ioo (0:ℝ) 1`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this assertion to establish
convergence along the specified source filter to the specified limit: `Tendsto ellipticLegendre
(𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem complementary_mem {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) : complementary k ∈ Ioo (0:ℝ) 1 := by
  have hp : 0 < 1-k^2 := by nlinarith [hk.1,hk.2]
  constructor
  · exact sqrt_pos.mpr hp
  · change sqrt (1-k^2) < 1
    simpa only [sqrt_one] using sqrt_lt_sqrt hp.le (show 1-k^2 < 1 by nlinarith [hk.1])

/--
Exact identity `complementary k^2=1-k^2`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_derivative` rewrites with this identity to
establish the actual derivative at the stated point: `HasDerivAt ellipticLegendre 0 k`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem complementary_square {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) : complementary k^2=1-k^2 :=
  sq_sqrt (by nlinarith [hk.1,hk.2])

/--
The actual derivative at the stated point: `HasDerivAt complementary (-k/complementary k) k`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt ellipticLegendre 0 k`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem complementary_derivative {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) :
    HasDerivAt complementary (-k/complementary k) k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hp : 0 < 1-k^2 := by nlinarith [hk.1,hk.2]
  have hd := ((hasDerivAt_const k (1:ℝ)).sub ((hasDerivAt_id k).pow 2)).sqrt hp.ne'
  convert hd using 1
  · funext y; rfl
  · dsimp [complementary]
    field_simp
    ring

/--
The actual derivative at the stated point: `HasDerivAt ellipticLegendre 0 k`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_constant` uses this derivative formula to
establish exact identity `ellipticLegendre k=ellipticLegendre (1/2)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ellipticLegendre_derivative {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) :
    HasDerivAt ellipticLegendre 0 k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hk' : |k| < 1 := by rw [abs_of_pos hk.1]; exact hk.2
  have hc := complementary_mem hk
  have hc' : |complementary k| < 1 := by rw [abs_of_pos hc.1]; exact hc.2
  have dc := complementary_derivative hk
  have dk := (ellipticK_deriv hc').comp k dc
  have de := (ellipticE_derivative hc').comp k dc
  have hd := (((ellipticE_derivative hk').mul dk).add ((ellipticK_deriv hk').mul de)).sub
    ((ellipticK_deriv hk').mul dk)
  convert hd using 1
  · rfl
  · dsimp [ellipticE₁]
    rw [ellipticE_eq k hk',ellipticE_eq (complementary k) hc']
    have hcs : 1-complementary k^2=k^2 := by rw [complementary_square hk]; ring
    rw [hcs]
    field_simp [hc.1.ne']
    ring_nf
    rw [complementary_square hk]
    ring

/--
Exact identity `ellipticLegendre k=ellipticLegendre (1/2)`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_identity` uses this identity to establish
exact identity `ellipticLegendre k=π/2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: A vanishing derivative makes the relevant function constant on the connected interval.
-/
theorem ellipticLegendre_constant {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) :
    ellipticLegendre k=ellipticLegendre (1/2) := by
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun k hk => (ellipticLegendre_derivative hk).differentiableAt.differentiableWithinAt)
    (fun k hk => (ellipticLegendre_derivative hk).deriv)
  exact (hc k hk).trans (hc (1/2) (by norm_num)).symm

/--
The stated quantitative bound `k*ellipticK (complementary k) ≤ π/2`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto ellipticLegendre
(𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem complementary_K_bound {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) :
    k*ellipticK (complementary k) ≤ π/2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hx : 1-k^2 ∈ Ico (0:ℝ) 1 := ⟨by nlinarith [hk.1,hk.2],by nlinarith [hk.1]⟩
  have hu := (ellipticA_bounds hx).2
  change (2/π)*ellipticK (complementary k) ≤ 1/sqrt (1-(1-k^2)) at hu
  rw [show 1-(1-k^2)=k^2 by ring,sqrt_sq hk.1.le] at hu
  have hh := mul_le_mul_of_nonneg_left hu (mul_pos (half_pos pi_pos) hk.1).le
  have hleft : (π/2*k)*((2/π)*ellipticK (complementary k))=k*ellipticK (complementary k) := by field_simp
  have hright : (π/2*k)*(1/k)=π/2 := by field_simp [hk.1.ne']
  rwa [hleft,hright] at hh

/--
Exact identity `ellipticE₁ 0=0`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto ellipticLegendre
(𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ellipticE₁_zero : ellipticE₁ 0=0 := by simp [ellipticE₁,ellipticK₁,ellipticIntegrand₁]

/--
Continuity at the stated point: `ContinuousAt ellipticE₁ k`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_boundary` uses this continuity result to
establish convergence along the specified source filter to the specified limit: `Tendsto
ellipticLegendre (𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.ellipticK₁_deriv`,
`chebyshev1.SineJacobi.ellipticK_deriv` with the arguments shown in the proof.
-/
theorem ellipticE₁_continuousAt {k : ℝ} (hk : |k| < 1) : ContinuousAt ellipticE₁ k :=
  ((continuousAt_const.sub (continuousAt_id.pow 2)).mul (ellipticK₁_deriv hk).continuousAt).sub
    (continuousAt_id.mul (ellipticK_deriv hk).continuousAt)

/--
Convergence along the specified source filter to the specified limit: `Tendsto ellipticLegendre
(𝓝[>] (0:ℝ)) (𝓝 (π/2))`.

Use: `chebyshev2.SineContinuum.ellipticLegendre_identity` uses this limit to establish
exact identity `ellipticLegendre k=π/2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection. Prove equality of functions by evaluating both sides at
an arbitrary argument.
-/
theorem ellipticLegendre_boundary :
    Tendsto ellipticLegendre (𝓝[>] (0:ℝ)) (𝓝 (π/2)) := by
  -- Record the convergence h0 with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have h0 : Tendsto (fun k : ℝ => k) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- Record the convergence hc with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hc : Tendsto complementary (𝓝[>] (0:ℝ)) (𝓝 1) := by
    change Tendsto (fun k : ℝ => sqrt (1-k^2)) (𝓝[>] (0:ℝ)) (𝓝 1)
    have h := continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1:ℝ))).sub (h0.pow 2))
    simpa only [zero_pow (by norm_num : 2 ≠ 0),sub_zero,sqrt_one,Function.comp_def] using h
  -- Record the convergence hE₁ with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hE₁ : Tendsto ellipticE₁ (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [ellipticE₁_zero,Function.comp_def] using
      (ellipticE₁_continuousAt (k := 0) (by norm_num)).tendsto.comp h0
  -- Record the convergence hres with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hres : Tendsto (fun k => (ellipticE k-ellipticK k)*ellipticK (complementary k))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using (tendsto_const_nhds (x := π/2)).mul hE₁.norm)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with k hk
    have hk' : |k| < 1 := by rw [abs_of_pos hk.1]; exact hk.2
    have hcp := complementary_mem hk
    have hcp' : |complementary k| < 1 := by rw [abs_of_pos hcp.1]; exact hcp.2
    have hp : 0 ≤ k*ellipticK (complementary k) :=
      mul_nonneg hk.1.le (ellipticK_pos _ hcp').le
    have he : (ellipticE k-ellipticK k)*ellipticK (complementary k)=
        ellipticE₁ k*(k*ellipticK (complementary k)) := by rw [ellipticE_difference k hk']; ring
    rw [he,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
    have hb := mul_le_mul_of_nonneg_left (complementary_K_bound hk) (abs_nonneg (ellipticE₁ k))
    simpa only [mul_comm,Real.norm_eq_abs] using hb
  have hK := (ellipticK_continuousAt (k := 0) (by norm_num)).tendsto.comp h0
  have hE := (ellipticE_continuous.tendsto 1).comp hc
  have hf := (hK.mul hE).add hres
  have he : ellipticLegendre=(fun k => ellipticK k*ellipticE (complementary k)+
      (ellipticE k-ellipticK k)*ellipticK (complementary k)) := by
    funext k
    dsimp [ellipticLegendre]
    ring
  rw [he]
  simpa only [ellipticK_zero,ellipticE_one,mul_one,add_zero,Function.comp_def] using hf

/--
Legendre's complementary elliptic-integral identity, with its exact constant obtained from
genuine integral endpoint limits.

Exact identity `ellipticLegendre k=π/2`.

Use:
`_private.chebyshev2.SineContinuum.Wronskian.0.chebyshev2.SineContinuum.midpoint_product`
uses this identity to establish the identity `(sqrt 2/2)*ellipticK (sqrt 2/2)*ellipticK₁
(sqrt 2/2)=π/2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem ellipticLegendre_identity {k : ℝ} (hk : k ∈ Ioo (0:ℝ) 1) : ellipticLegendre k=π/2 := by
  have hc : Tendsto ellipticLegendre (𝓝[>] (0:ℝ)) (𝓝 (ellipticLegendre (1/2))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with k hk
    exact (ellipticLegendre_constant hk).symm
  exact (ellipticLegendre_constant hk).trans (tendsto_nhds_unique hc ellipticLegendre_boundary)

end
end chebyshev2.SineContinuum
