import chebyshev2.Sobolev.CausalKernel

/-!
Article: chebyshev2, Theorem 3.1.
The L2 derivative candidate u'=g-u.
Use: `chebyshev2.Sobolev.causalValue_memLp` feeds `chebyshev2.Sobolev.causalValue_sobolev`
(causal Value sobolev).
Proof chain: `chebyshev2.GroundState.GroundWitness.square_identity` — chebyshev2, Theorem 3.1;
Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace chebyshev2.Sobolev
noncomputable section
open chebyshev2.Continuum Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `‖g‖^2 = ∫ x, g x^2`.

Use: `chebyshev2.Sobolev.causalValueLp_norm_le` rewrites with this identity to establish
the stated quantitative bound `‖causalValueLp g‖ ≤ ‖g‖`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem l2_norm_sq (g : FeatureSpace) : ‖g‖^2 = ∫ x, g x^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]

/--
Fubini for the weighted square bound. Both row and column kernel masses are one; this gives a
genuine global L2 estimate on the representative.

Integrability of the displayed function: `Integrable (fun z : ℝ × ℝ => causalKernel z.1 z.2*g
z.2^2) (volume.prod volume)`.

Use: `chebyshev2.Sobolev.causalSquare_integral` rewrites with this integrability result to
establish exact identity `(∫ x, ∫ t, causalKernel x t*g t^2) = ∫ t, g t^2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalKernel_joint_measurable`,
`chebyshev2.Sobolev.causalKernel_column_integrable`,
`chebyshev2.Sobolev.causalKernel_nonneg` with the arguments shown in the proof.
-/
theorem causalSquare_integrable_prod (g : FeatureSpace) :
    Integrable (fun z : ℝ × ℝ => causalKernel z.1 z.2*g z.2^2) (volume.prod volume) := by
  -- Use the identities/estimates `chebyshev2.Sobolev.causalKernel_joint_measurable`,
  -- `chebyshev2.Sobolev.causalKernel_column_integrable`,
  -- `chebyshev2.Sobolev.causalKernel_nonneg` with the arguments shown in the proof.
  have hs : StronglyMeasurable (fun z : ℝ × ℝ => causalKernel z.1 z.2*g z.2^2) :=
    causalKernel_joint_measurable.stronglyMeasurable.mul
      (((Lp.stronglyMeasurable g).comp_measurable measurable_snd).pow 2)
  apply (integrable_prod_iff' hs.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => (causalKernel_column_integrable t).mul_const (g t^2))
  · have he (t : ℝ) : (∫ x, ‖causalKernel x t*g t^2‖) = g t^2 := by
      have hn (x : ℝ) : ‖causalKernel x t*g t^2‖ = causalKernel x t*g t^2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (causalKernel_nonneg x t) (sq_nonneg _))]
      simp_rw [hn]
      rw [integral_mul_const, causalKernel_column_mass, one_mul]
    simpa only [he] using (Lp.memLp g).integrable_sq

/--
Exact identity `(∫ x, ∫ t, causalKernel x t*g t^2) = ∫ t, g t^2`.

Use: `chebyshev2.Sobolev.causalValueLp_norm_le` uses this identity to establish the stated
quantitative bound `‖causalValueLp g‖ ≤ ‖g‖`.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Establish the required integrability/summability obligations before exchanging integrals
or sums.
-/
theorem causalSquare_integral (g : FeatureSpace) :
    (∫ x, ∫ t, causalKernel x t*g t^2) = ∫ t, g t^2 := by
  rw [integral_integral_swap (causalSquare_integrable_prod g)]
  simp_rw [integral_mul_const, causalKernel_column_mass, one_mul]

/--
Integrability of the displayed function: `Integrable (fun x => causalValue g x^2)`.

Use: `chebyshev2.Sobolev.causalValueLp_norm_le` uses this integrability result to establish
the stated quantitative bound `‖causalValueLp g‖ ≤ ‖g‖`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Establish the required integrability/summability obligations before exchanging integrals
or sums.
-/
theorem causalValue_square_integrable (g : FeatureSpace) : Integrable (fun x => causalValue g x^2) := by
  apply (causalSquare_integrable_prod g).integral_prod_left.mono'
  · exact (causalValue_continuous g).pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact causalValue_sq_bound g x)

/--
The precise assertion is `MemLp (causalValue g) 2 volume`.

Use: `chebyshev2.Sobolev.causalValueLp` uses this assertion in the displayed construction
of `causalValueLp`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalValue_continuous`,
`chebyshev2.Sobolev.causalValue_square_integrable` with the arguments shown in the proof.
-/
theorem causalValue_memLp (g : FeatureSpace) : MemLp (causalValue g) 2 volume :=
  (memLp_two_iff_integrable_sq (causalValue_continuous g).aestronglyMeasurable).mpr
    (causalValue_square_integrable g)

/--
Defines `causalValueLp` of type `FeatureSpace` by `(causalValue_memLp g).toLp (causalValue g)`.

Use: `chebyshev2.Sobolev.causalDerivativeLp` uses this definition in the displayed
construction of `causalDerivativeLp`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def causalValueLp (g : FeatureSpace) : FeatureSpace := (causalValue_memLp g).toLp (causalValue g)

/--
The precise assertion is `causalValueLp g =ᵐ[volume] causalValue g`.

Use: `chebyshev2.Sobolev.causalDerivativeLp_coe` uses this identity to establish the stated
quantitative bound `causalDerivativeLp g =ᵐ[volume] (fun x => g x-causalValue g x)`.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalValue_memLp` with the
arguments shown in the proof.
-/
theorem causalValueLp_coe (g : FeatureSpace) : causalValueLp g =ᵐ[volume] causalValue g :=
  (causalValue_memLp g).coeFn_toLp

/--
The stated quantitative bound `‖causalValueLp g‖ ≤ ‖g‖`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Establish the required integrability/summability obligations before exchanging integrals
or sums. Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem causalValueLp_norm_le (g : FeatureSpace) : ‖causalValueLp g‖ ≤ ‖g‖ := by
  -- Establish the required integrability/summability obligations before exchanging integrals
  -- or sums.
  have h : ‖causalValueLp g‖^2 ≤ ‖g‖^2 := by
    rw [l2_norm_sq, l2_norm_sq]
    have he : (fun x => causalValueLp g x^2) =ᵐ[volume] (fun x => causalValue g x^2) :=
      (causalValueLp_coe g).fun_comp (fun x => x^2)
    rw [integral_congr_ae he]
    exact (integral_mono_ae (causalValue_square_integrable g)
      (causalSquare_integrable_prod g).integral_prod_left
      (Filter.Eventually.of_forall (causalValue_sq_bound g))).trans_eq (causalSquare_integral g)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/--
The L2 derivative candidate u'=g-u. Its equality with the actual almost everywhere derivative
is the next analytic layer.

Use: `chebyshev2.Sobolev.causalDerivativeLp_coe` rewrites with this definition to establish
the stated quantitative bound `causalDerivativeLp g =ᵐ[volume] (fun x => g x-causalValue g x)`.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
def causalDerivativeLp (g : FeatureSpace) : FeatureSpace := g-causalValueLp g

/--
The stated quantitative bound `causalDerivativeLp g =ᵐ[volume] (fun x => g x-causalValue g x)`.

Use: `chebyshev2.Sobolev.causalValue_energy_Lp` uses this identity to establish exact
identity `‖causalValueLp g‖^2+‖causalDerivativeLp g‖^2=‖g‖^2`.

Article: chebyshev2, Theorem 3.1.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem causalDerivativeLp_coe (g : FeatureSpace) :
    causalDerivativeLp g =ᵐ[volume] (fun x => g x-causalValue g x) := by
  filter_upwards [Lp.coeFn_sub g (causalValueLp g), causalValueLp_coe g] with x hx hu
  rw [causalDerivativeLp, hx, Pi.sub_apply, hu]

end
end chebyshev2.Sobolev
