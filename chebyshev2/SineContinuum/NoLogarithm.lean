import chebyshev2.SineContinuum.SineHilbertBasis

/-!
Article: chebyshev2, Lemma 5.
Equality on the entire operator domain, not just on basis vectors.
Use: `chebyshev2.SineContinuum.sineUnitary_domain_iff` feeds
`chebyshev2.SineContinuum.legendreV_domain` (legendre V domain).
Proof chain: `chebyshev2.SineContinuum.legendreV_domain` — chebyshev2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace chebyshev2.SineContinuum
noncomputable section
set_option backward.isDefEq.respectTransparency true

/--
Exact identity `sineHilbertBasis.repr (sineUnitary u)=legendreHilbertBasis.repr u`.

Use: `chebyshev2.SineContinuum.sineUnitary_domain_iff` rewrites with this identity to
establish equivalence of the displayed criteria: `sineUnitary u ∈ sineOperator.domain ↔ u ∈
legendreOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem sineUnitary_repr (u : LegendreSpace) :
    sineHilbertBasis.repr (sineUnitary u)=legendreHilbertBasis.repr u := by
  change legendreHilbertBasis.repr (sineUnitary.symm (sineUnitary u))=_
  rw [sineUnitary.symm_apply_apply]

/--
Exact identity `legendreHilbertBasis.repr (sineUnitary.symm u)=sineHilbertBasis.repr u`.

Use: `chebyshev2.SineContinuum.sineUnitary_domain_iff` rewrites with this identity to
establish equivalence of the displayed criteria: `sineUnitary u ∈ sineOperator.domain ↔ u ∈
legendreOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineUnitary_repr` with the
arguments shown in the proof.
-/
theorem sineUnitary_symm_repr (u : LegendreSpace) :
    legendreHilbertBasis.repr (sineUnitary.symm u)=sineHilbertBasis.repr u := by rw [← sineUnitary_repr,sineUnitary.apply_symm_apply]

/--
Exact identity `mu j=Real.pi^2*((j:ℝ)*(j+1)+1/4)`.

Use: `chebyshev2.SineContinuum.sineUnitary_domain_iff` rewrites with this identity to
establish equivalence of the displayed criteria: `sineUnitary u ∈ sineOperator.domain ↔ u ∈
legendreOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem mu_legendre (j : ℕ) : mu j=Real.pi^2*((j:ℝ)*(j+1)+1/4) := by
  unfold mu
  ring

/--
The precise assertion is `Continuum.UnboundedDiagonalGraph sineHilbertBasis mu (sineUnitary
(u:LegendreSpace)) (Real.pi^2 • sineUnitary (legendreOperator u+(1/4:ℝ) • (u:LegendreSpace)))`.

Use: `chebyshev2.SineContinuum.sineOperator_conjugacy` uses this assertion to establish the
precise assertion is `sineOperator ⟨sineUnitary (u:LegendreSpace),sineUnitary_domain_forward
u⟩= Real.pi^2 • sineUnitary (legendreOperator u+(1/4:ℝ) • (u:LegendreSpace))`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_operator`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineUnitary_repr`,
`chebyshev2.Continuum.unboundedDiagonalOperator_graph`,
`chebyshev2.SineContinuum.mu_legendre` with the arguments shown in the proof.
-/
theorem sineUnitary_graph (u : legendreOperator.domain) :
    Continuum.UnboundedDiagonalGraph sineHilbertBasis mu (sineUnitary (u:LegendreSpace))
      (Real.pi^2 • sineUnitary (legendreOperator u+(1/4:ℝ) • (u:LegendreSpace))) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.sineUnitary_repr`,
  -- `chebyshev2.Continuum.unboundedDiagonalOperator_graph`,
  -- `chebyshev2.SineContinuum.mu_legendre` with the arguments shown in the proof.
  intro j
  simp only [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,sineUnitary_repr,
    map_add,lp.coeFn_add,Pi.add_apply]
  have h := Continuum.unboundedDiagonalOperator_graph legendreHilbertBasis
    (fun n => (n:ℝ)*(n+1)) u j
  change legendreHilbertBasis.repr (legendreOperator u) j=
    (j:ℝ)*(j+1)*legendreHilbertBasis.repr (u:LegendreSpace) j at h
  rw [h,mu_legendre]
  ring

/--
Membership in the specified domain/enclosure: `sineUnitary (u:LegendreSpace) ∈
sineOperator.domain`.

Use: `chebyshev2.SineContinuum.sineUnitary_domain_iff` uses this assertion to establish
equivalence of the displayed criteria: `sineUnitary u ∈ sineOperator.domain ↔ u ∈
legendreOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_operator`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sineUnitary_graph` with the
arguments shown in the proof.
-/
theorem sineUnitary_domain_forward (u : legendreOperator.domain) :
    sineUnitary (u:LegendreSpace) ∈ sineOperator.domain :=
  ⟨_,sineUnitary_graph u⟩

/--
Equality on the entire operator domain, not just on basis vectors. The Legendre side uses the
equivalent shifted unit-interval coordinate.

The precise assertion is `sineOperator ⟨sineUnitary
(u:LegendreSpace),sineUnitary_domain_forward u⟩= Real.pi^2 • sineUnitary (legendreOperator
u+(1/4:ℝ) • (u:LegendreSpace))`.

Use: `chebyshev2.SineContinuum.legendreV_operator` uses this identity to establish the
precise assertion is `sineOperator ⟨legendreV (u:StandardSpace),(legendreV_domain _).mpr
u.property⟩= π^2 • legendreV (standardLegendreOperator u+(1/4:ℝ) • (u:StandardSpace))`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_operator`.

Proof: Use the identities/estimates `chebyshev2.Continuum.UnboundedDiagonalGraph.unique`,
`chebyshev2.Continuum.unboundedDiagonalOperator_graph`,
`chebyshev2.SineContinuum.sineUnitary_graph` with the arguments shown in the proof.
-/
theorem sineOperator_conjugacy (u : legendreOperator.domain) :
    sineOperator ⟨sineUnitary (u:LegendreSpace),sineUnitary_domain_forward u⟩=
      Real.pi^2 • sineUnitary (legendreOperator u+(1/4:ℝ) • (u:LegendreSpace)) := by
  apply Continuum.UnboundedDiagonalGraph.unique
    (Continuum.unboundedDiagonalOperator_graph sineHilbertBasis mu _)
  exact sineUnitary_graph u

/--
Equivalence of the displayed criteria: `sineUnitary u ∈ sineOperator.domain ↔ u ∈
legendreOperator.domain`.

Use: `chebyshev2.SineContinuum.legendreV_domain` uses this assertion to establish
equivalence of the displayed criteria: `legendreV u ∈ sineOperator.domain ↔ u ∈
standardLegendreOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem sineUnitary_domain_iff (u : LegendreSpace) :
    sineUnitary u ∈ sineOperator.domain ↔ u ∈ legendreOperator.domain := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  constructor
  · intro hu
    let v := sineOperator ⟨sineUnitary u,hu⟩
    refine ⟨(Real.pi^2)⁻¹ • sineUnitary.symm v-(1/4:ℝ) • u,?_⟩
    intro j
    simp only [map_sub,lp.coeFn_sub,Pi.sub_apply,map_smul,lp.coeFn_smul,
      Pi.smul_apply,smul_eq_mul,sineUnitary_symm_repr]
    have h := Continuum.unboundedDiagonalOperator_graph sineHilbertBasis mu
      (⟨sineUnitary u,hu⟩ : sineOperator.domain) j
    change sineHilbertBasis.repr v j=mu j*sineHilbertBasis.repr (sineUnitary u) j at h
    rw [sineUnitary_repr] at h
    rw [h,mu_legendre]
    have hp : Real.pi^2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    field_simp [hp]
    ring
  · intro hu
    exact sineUnitary_domain_forward ⟨u,hu⟩

end
end chebyshev2.SineContinuum
