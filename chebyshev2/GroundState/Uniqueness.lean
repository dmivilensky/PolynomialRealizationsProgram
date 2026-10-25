import chebyshev2.GroundState.SquareEquality

/-!
Article: chebyshev2, Theorem 3.1.
Simplicity on the actual Sobolev feature operator and uniqueness of every H1 classical ODE solution,
together with the complete square equality case.
Use: `chebyshev2.GroundState.exists_unique_ground` feeds
`chebyshev2.GroundState.kernel_ground_simple` (The literal leading eigenspace of the article's
L2 kernel has dimension one).
Proof chain: `chebyshev2.GroundState.ground_state` — chebyshev2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Continuum chebyshev2.Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
A classical/AE ODE solution in H1 satisfies the exact energy equation. The boundary term v*v'
is handled by its actual L1 integrability and local AC.

Exact identity `‖v‖^2=c*(∫ x, m x*H1.rep v x^2)`.

Use: `chebyshev2.GroundState.exists_unique_ground` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.unique_solution`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem ode_energy {m : ℝ → ℝ} (hm : Integrable m) (c : ℝ) (v : H1) {d : ℝ → ℝ}
    (hvd : ∀ᵐ x, HasDerivAt (H1.rep v) (d x) x)
    (hdac : ∀ a b, AbsolutelyContinuousOnInterval d a b)
    (hode : ∀ᵐ x, HasDerivAt d ((1-c*m x)*H1.rep v x) x) :
    ‖v‖^2=c*(∫ x, m x*H1.rep v x^2) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hd : H1.slope v =ᵐ[volume] d := by
    filter_upwards [(H1.regular v).derivative_ae,hvd] with x hx hy
    exact hx.unique hy
  have hdm : MemLp d 2 volume := (H1.regular v).derivative_memLp.ae_eq hd
  let D : ℝ → ℝ := fun x => (d x^2+H1.rep v x^2)-c*(m x*H1.rep v x^2)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable D := (hdm.integrable_sq.add (H1.regular v).value_memLp.integrable_sq).sub
    ((weighted_square_integrable hm v).const_mul c)
  have hz : (∫ x, D x)=0 := by
    apply locallyAC_integral_derivative_zero (l2_product_integrable (H1.regular v).value_memLp hdm) hi
    · intro a b
      apply (((H1.regular v).locally_ac a b).mul (hdac a b)).congr
      intro x _
      rfl
    · filter_upwards [hvd,hode] with x hx hy
      convert hx.mul hy using 1
      dsimp [D]
      ring
  change (∫ x, (d x^2+H1.rep v x^2)-c*(m x*H1.rep v x^2))=0 at hz
  have hsq : (fun x => d x^2) =ᵐ[volume] (fun x => H1.slope v x^2) :=
    hd.symm.fun_comp (fun x => x^2)
  -- Establish hE as the integrability justification for the later integral estimates or
  -- changes of order.
  have hE : Integrable (fun x => d x^2+H1.rep v x^2) :=
    hdm.integrable_sq.add (H1.regular v).value_memLp.integrable_sq
  rw [integral_sub hE
    ((weighted_square_integrable hm v).const_mul c),
    integral_add hdm.integrable_sq (H1.regular v).value_memLp.integrable_sq,
    integral_congr_ae hsq,← H1.norm_sq_energy,integral_const_mul] at hz
  exact sub_eq_zero.mp hz

/--
Exact identity `‖v‖^2=groundParameter hm hn*(∫ x, m x*H1.rep v x^2)`.

Use: `chebyshev2.GroundState.exists_unique_ground` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.ground_eigenfunction_weak_equation`,
`chebyshev2.Sobolev.H1.norm_sq_energy` with the arguments shown in the proof.
-/
theorem density_ground_energy {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) {v : H1}
    (he : densityOperator m v=kernelEigenvalue hm hn 0 • v) :
    ‖v‖^2=groundParameter hm hn*(∫ x, m x*H1.rep v x^2) := by
  have h := ground_eigenfunction_weak_equation hm hn hM he v
  simp_rw [mul_assoc,← pow_two] at h
  rw [← H1.norm_sq_energy] at h
  exact h

/--
Simplicity on the actual Sobolev feature operator and uniqueness of every H1 classical ODE
solution, together with the complete square equality case.

Use: `chebyshev2.GroundState.ground_state` uses this identity to establish the precise
assertion is `Nonempty (GroundWitness hm hn)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: Use the identities/estimates `chebyshev2.GroundState.exists_ground_square_identity`,
`chebyshev2.GroundState.RiccatiData.residual_integral_eq_zero_iff_smul`,
`chebyshev2.GroundState.RiccatiData.square_identity` with the arguments shown in the proof.
-/
theorem exists_unique_ground {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : ∃ (u : H1) (R : RiccatiData m (groundParameter hm hn)),
      (∀ x, 0 < H1.rep u x) ∧
      (∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) ∧
      densityOperator m u=kernelEigenvalue hm hn 0 • u ∧
      (∀ f : H1, (∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=0 ↔ ∃ r : ℝ, f=r • u) ∧
      (∀ v : H1, densityOperator m v=kernelEigenvalue hm hn 0 • v → ∃ r : ℝ, v=r • u) ∧
      (∀ (v : H1) (d : ℝ → ℝ),
        (∀ᵐ x, HasDerivAt (H1.rep v) (d x) x) →
        (∀ a b, AbsolutelyContinuousOnInterval d a b) →
        (∀ᵐ x, HasDerivAt d ((1-groundParameter hm hn*m x)*H1.rep v x) x) →
        ∃ r : ℝ, v=r • u) := by
  -- Use the identities/estimates `chebyshev2.GroundState.exists_ground_square_identity`,
  -- `chebyshev2.GroundState.RiccatiData.residual_integral_eq_zero_iff_smul`,
  -- `chebyshev2.GroundState.RiccatiData.square_identity` with the arguments shown in the
  -- proof.
  obtain ⟨u,R,hpos,hdu,_,he⟩ := exists_ground_square_identity hm hn hM
  refine ⟨u,R,hpos,hdu,he,R.residual_integral_eq_zero_iff_smul hpos hdu,?_,?_⟩
  · intro v hv
    apply (R.residual_integral_eq_zero_iff_smul hpos hdu v).mp
    rw [R.square_identity hm,density_ground_energy hm hn hM hv,sub_self]
  · intro v d hvd hdac hode
    apply (R.residual_integral_eq_zero_iff_smul hpos hdu v).mp
    rw [R.square_identity hm,ode_energy hm _ v hvd hdac hode,sub_self]

end
end chebyshev2.GroundState
