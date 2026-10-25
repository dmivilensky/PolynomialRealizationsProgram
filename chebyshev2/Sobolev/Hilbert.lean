import chebyshev2.Sobolev.Representation
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
Article: chebyshev2, Theorem 6.1.
The article's k_x=e^{-|·-x|}/2, in exact H1 coordinates.
Use: `chebyshev2.Sobolev.H1.evaluation_bound` feeds
`chebyshev2.GroundState.weighted_square_integrable` (weighted square integrable).
Proof chain: `chebyshev2.LocalObstruction.sine_ground_square_tail` — chebyshev2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace chebyshev2.Sobolev
noncomputable section
open chebyshev2.Continuum Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

/--
H1 in integrating-factor coordinates. `H1.rep` is the unique continuous Sobolev representative;
`H1.range_iff` proves that these coordinates cover the literal H1 space, and `H1.inner_energy`
identifies its actual integral inner product.

Use: `chebyshev2.Sobolev.H1.continuous_rep` uses this definition to establish continuity of
the displayed function: `Continuous (rep u)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
abbrev H1 := FeatureSpace

/--
The precise assertion is `TopologicalSpace.SeparableSpace H1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 4.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem h1_separable : TopologicalSpace.SeparableSpace H1 := inferInstance
/--
The precise assertion is `CompleteSpace H1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 4.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem h1_complete : CompleteSpace H1 := inferInstance

namespace H1

/--
Defines `rep` of type `ℝ → ℝ` by `causalValue u`.

Use: `chebyshev2.Sobolev.H1.inner_energy` uses this definition to establish the identity
`inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.groundParameter_variational`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def rep (u : H1) : ℝ → ℝ := causalValue u
/--
Defines `slope` of type `ℝ → ℝ` by `fun x => u x-rep u x`.

Use: `chebyshev2.Sobolev.H1.inner_energy` rewrites with this definition to establish exact
identity `inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def slope (u : H1) : ℝ → ℝ := fun x => u x-rep u x

/--
The precise assertion is `SobolevRegular (rep u) (slope u)`.

Use: `chebyshev2.Sobolev.H1.inner_energy` rewrites with this assertion to establish exact
identity `inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalValue_sobolev` with the
arguments shown in the proof.
-/
theorem regular (u : H1) : SobolevRegular (rep u) (slope u) := causalValue_sobolev u
/--
Continuity of the displayed function: `Continuous (rep u)`.

Use: `chebyshev2.Comparison.groundSlope_c1` uses this continuity result to establish
smoothness to the stated order: `ContDiff ℝ 1 G.d`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalValue_continuous` with the
arguments shown in the proof.
-/
theorem continuous_rep (u : H1) : Continuous (rep u) := causalValue_continuous u
/--
Convergence along the specified source filter to the specified limit: `Tendsto (rep u) atTop (𝓝
0) ∧ Tendsto (rep u) atBot (𝓝 0)`.

Use: `chebyshev2.GroundState.RiccatiData.q_not_two_atBot` uses this limit to establish the
precise assertion is `¬ Tendsto R.q atBot (𝓝 2)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.groundProfile_left_limit`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.SobolevRegular.tendsto_zero`,
`chebyshev2.Sobolev.H1.regular` with the arguments shown in the proof.
-/
theorem rep_tendsto_zero (u : H1) :
    Tendsto (rep u) atTop (𝓝 0) ∧ Tendsto (rep u) atBot (𝓝 0) := (regular u).tendsto_zero

/--
Equivalence of the displayed criteria: `(∃ u : H1, rep u=f) ↔ ∃ d, SobolevRegular f d`.

Use: `chebyshev2.Comparison.reflectedGround_exists` uses this identity to establish
constructs witnesses with the exact properties `∃ v : H1, H1.rep v=fun x => H1.rep G.u (-x)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.regular`,
`chebyshev2.Sobolev.SobolevRegular.causal_representation` with the arguments shown in the
proof.
-/
theorem range_iff (f : ℝ → ℝ) :
    (∃ u : H1, rep u=f) ↔ ∃ d, SobolevRegular f d := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨slope u, regular u⟩
  · rintro ⟨d,hd⟩
    obtain ⟨u,hu,_⟩ := hd.causal_representation
    exact ⟨u,hu.symm⟩

/--
Exact identity `rep (u+v)=fun x => rep u x+rep v x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rep_add (u v : H1) : rep (u+v)=fun x => rep u x+rep v x := by
  funext x
  simp [rep, causalValue, inner_add_right, mul_add]

/--
Exact identity `rep (c • u)=fun x => c*rep u x`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_unique` rewrites with this identity
to establish the identity `1-e x/H1.rep v x=G.q x`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_eq_zero_iff`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rep_smul (c : ℝ) (u : H1) : rep (c • u)=fun x => c*rep u x := by
  funext x
  simp [rep, causalValue, real_inner_smul_right, mul_left_comm]

/--
Exact identity `rep (0 : H1)=0`.

Use: `chebyshev2.Comparison.groundParameter_reflection` rewrites with this identity to
establish exact identity `groundParameter (reflected_integrable hm) (reflected_nonneg
hn)=groundParameter hm hn`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.kernel_ground_simple`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rep_zero : rep (0 : H1)=0 := by
  funext x
  simp [rep, causalValue]

/--
The precise assertion is `Function.Injective rep`.

Use: `chebyshev2.GroundState.RiccatiData.eq_smul_of_residual_zero` uses this assertion to
establish constructs witnesses with the exact properties `∃ r : ℝ, f=r • u`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_eq_zero_iff`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem rep_injective : Function.Injective rep := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro u v huv
  have ha : ∀ᵐ x, HasDerivAt (rep u) (u x-rep u x) x := (regular u).derivative_ae
  have hb : ∀ᵐ x, HasDerivAt (rep u) (v x-rep u x) x := by
    simpa only [slope, ← huv] using (regular v).derivative_ae
  apply Lp.ext
  filter_upwards [ha,hb] with x hx hy
  have he := hx.unique hy
  linarith

/--
Exact identity `‖u‖^2=(∫ x, slope u x^2)+(∫ x, rep u x^2)`.

Use: `chebyshev2.GroundState.RiccatiData.square_identity` rewrites with this identity to
establish the precise assertion is `(∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)= ‖f‖^2-c*(∫ x, m
x*H1.rep f x^2)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalValue_energy` with the
arguments shown in the proof.
-/
theorem norm_sq_energy (u : H1) :
    ‖u‖^2=(∫ x, slope u x^2)+(∫ x, rep u x^2) := by simpa only [rep, slope, add_comm] using (causalValue_energy u).symm

/--
Integrability of the displayed function: `Integrable (fun x => slope u x*rep v x+rep u x*slope
v x)`.

Use: `chebyshev2.Sobolev.H1.inner_energy` rewrites with this integrability result to
establish exact identity `inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.l2_product_integrable`,
`chebyshev2.Sobolev.H1.regular` with the arguments shown in the proof.
-/
theorem product_derivative_integrable (u v : H1) :
    Integrable (fun x => slope u x*rep v x+rep u x*slope v x) :=
  (l2_product_integrable (regular u).derivative_memLp (regular v).value_memLp).add
    (l2_product_integrable (regular u).value_memLp (regular v).derivative_memLp)

/--
Exact identity `(∫ x, slope u x*rep v x+rep u x*slope v x)=0`.

Use: `chebyshev2.Sobolev.H1.inner_energy` rewrites with this identity to establish exact
identity `inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem integral_product_derivative_zero (u v : H1) :
    (∫ x, slope u x*rep v x+rep u x*slope v x)=0 := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  apply locallyAC_integral_derivative_zero
    (l2_product_integrable (regular u).value_memLp (regular v).value_memLp)
    (product_derivative_integrable u v)
  · intro a b
    apply (((regular u).locally_ac a b).mul ((regular v).locally_ac a b)).congr
    intro x _
    rfl
  · filter_upwards [(regular u).derivative_ae,(regular v).derivative_ae] with x hx hy
    exact hx.mul hy

/--
Exact identity `inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x)`.

Use: `chebyshev2.GroundState.ground_eigenfunction_weak_equation` rewrites with this
identity to establish `(∫ x, H1.slope v x*H1.slope u x)+(∫ x, H1.rep v
x*H1.rep u x)= groundParameter hm hn*∫ x, m x*H1.rep v x*H1.rep u x`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.l2_product_integrable`,
`chebyshev2.Sobolev.H1.regular`, `chebyshev2.Sobolev.H1.product_derivative_integrable`
with the arguments shown in the proof.
-/
theorem inner_energy (u v : H1) :
    inner ℝ u v=(∫ x, slope u x*slope v x)+(∫ x, rep u x*rep v x) := by
  -- Use the identities/estimates `chebyshev2.Sobolev.l2_product_integrable`,
  -- `chebyshev2.Sobolev.H1.regular`,
  -- `chebyshev2.Sobolev.H1.product_derivative_integrable` with the arguments shown in the
  -- proof.
  rw [L2.inner_def]
  have he (x : ℝ) : inner ℝ (u x) (v x) =
      (slope u x*slope v x+rep u x*rep v x)+
        (slope u x*rep v x+rep u x*slope v x) := by
    simp only [RCLike.inner_apply, conj_trivial, slope]
    ring
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => slope u x*slope v x+rep u x*rep v x) :=
    (l2_product_integrable (regular u).derivative_memLp (regular v).derivative_memLp).add
      (l2_product_integrable (regular u).value_memLp (regular v).value_memLp)
  simp_rw [he]
  rw [integral_add hi (product_derivative_integrable u v),
    integral_product_derivative_zero, add_zero,
    integral_add (l2_product_integrable (regular u).derivative_memLp (regular v).derivative_memLp)
      (l2_product_integrable (regular u).value_memLp (regular v).value_memLp)]

/--
The article's k_x=e^{-|·-x|}/2, in exact H1 coordinates.

Use: `chebyshev2.Sobolev.H1.k_rep` rewrites with this definition to establish exact
identity `rep (k x) t=(1/2)*exp (-|t-x|)`.

Article: chebyshev2, Theorem 6.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def k (x : ℝ) : H1 := (sqrt 2)⁻¹ • feature x

/--
Exact identity `rep (k x) t=(1/2)*exp (-|t-x|)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem k_rep (x t : ℝ) : rep (k x) t=(1/2)*exp (-|t-x|) := by
  simp only [k, rep, causalValue, real_inner_smul_right, feature_inner]
  have hs : sqrt 2^2=2 := sq_sqrt (by norm_num)
  field_simp
  nlinarith

/--
Exact identity `inner ℝ (k x) u=rep u x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem reproducing (x : ℝ) (u : H1) : inner ℝ (k x) u=rep u x := by simp [k, rep, causalValue, real_inner_smul_left]

/--
Exact identity `rep (feature x) t=exp (-|t-x|)/sqrt 2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_inner` with the arguments
shown in the proof.
-/
theorem unitFeature_rep (x t : ℝ) : rep (feature x) t=exp (-|t-x|)/sqrt 2 := by simp [rep, causalValue, feature_inner, div_eq_mul_inv, mul_comm]

/--
The stated quantitative bound `|rep u x| ≤ ‖u‖/sqrt 2`.

Use: `chebyshev2.GroundState.weighted_square_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => m x*H1.rep u x^2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem evaluation_bound (u : H1) (x : ℝ) : |rep u x| ≤ ‖u‖/sqrt 2 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (feature x) u
  rw [feature_norm, one_mul] at h
  simp only [rep, causalValue, abs_mul, abs_inv, abs_of_nonneg (sqrt_nonneg _)]
  simpa only [div_eq_mul_inv, mul_comm, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (sqrt_nonneg 2))

end H1
end
end chebyshev2.Sobolev
