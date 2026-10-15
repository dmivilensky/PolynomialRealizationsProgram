import «2610.05164v2».SineContinuum.SineCoordinate
import «2610.05164v2».SineContinuum.LegendreOperator

/-!
Article: 2610.05164v2, Lemma 5.
The no-logarithm endpoint realization specified by the full diagonal basis domain, rather than
endpoint vanishing alone.
Use: `«2610.05164v2».SineContinuum.sineOperator` feeds
`«2610.05164v2».SineContinuum.greenOperator_sineOperator` (green Operator sine Operator).
Proof chain: `«2610.05164v2».SineContinuum.legendreV_domain` — 2610.05164v2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Real Set MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/--
The actual complete sine--Legendre Hilbert basis in Lebesgue L²(0,1).

Use: `«2610.05164v2».SineContinuum.sineOperator` uses this definition in the displayed
construction of `sineOperator`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
def sineHilbertBasis : HilbertBasis ℕ ℝ LegendreSpace :=
  HilbertBasis.ofRepr (sineUnitary.symm.trans legendreHilbertBasis.repr)

/--
Exact identity `sineHilbertBasis n=sineUnitary (legendreHilbertBasis n)`.

Use: `«2610.05164v2».SineContinuum.sineHilbertBasis_ae` rewrites with this identity to
establish exact identity `sineHilbertBasis n=ᵐ[volume] (fun t : LegendreInterval => upsilon n
t)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem sineHilbertBasis_apply (n : ℕ) : sineHilbertBasis n=sineUnitary (legendreHilbertBasis n) := rfl

/--
Exact identity `sineUnitary f=ᵐ[volume] (fun t : LegendreInterval => √(sineJacobian t)*f
(sineCoordinateEquiv t))`.

Use: `«2610.05164v2».SineContinuum.sineHilbertBasis_ae` uses this identity to establish exact
identity `sineHilbertBasis n=ᵐ[volume] (fun t : LegendreInterval => upsilon n t)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineUnitary_ae (f : LegendreSpace) :
    sineUnitary f=ᵐ[volume] (fun t : LegendreInterval =>
      √(sineJacobian t)*f (sineCoordinateEquiv t)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let g := Continuum.measureUnitary sineCoordinateEquiv sineCoordinate_measurePreserving f
  have hg := sineWeight.base_ac.ae_eq
    (Continuum.measureUnitary_ae sineCoordinateEquiv sineCoordinate_measurePreserving f)
  filter_upwards [sineWeight.mul_ae g,hg] with t hm hg
  change sineWeight.mul g t=_
  rw [hm,hg]
  rfl

/--
Exact identity `normalizedLegendre n=ᵐ[volume] (fun t : LegendreInterval =>
√(2*(n:ℝ)+1)*(shifted n).eval (t:ℝ))`.

Use: `«2610.05164v2».SineContinuum.sineHilbertBasis_ae` uses this identity to establish exact
identity `sineHilbertBasis n=ᵐ[volume] (fun t : LegendreInterval => upsilon n t)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem normalizedLegendre_ae (n : ℕ) : normalizedLegendre n=ᵐ[volume]
    (fun t : LegendreInterval => √(2*(n:ℝ)+1)*(shifted n).eval (t:ℝ)) := by
  filter_upwards [Lp.coeFn_smul √(2*(n:ℝ)+1) (polynomialL2 (shifted n)),
    polynomialL2_ae (shifted n)] with t hs hp
  change (√(2*(n:ℝ)+1) • polynomialL2 (shifted n)) t=_
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hp]

/--
Exact identity `√(sineJacobian
t)*√(2*(n:ℝ)+1)=√(π*((n:ℝ)+1/2))*«2606.16671v2».SineJacobi.profileWeight t`.

Use: `«2610.05164v2».SineContinuum.sineHilbertBasis_ae` rewrites with this identity to
establish exact identity `sineHilbertBasis n=ᵐ[volume] (fun t : LegendreInterval => upsilon n
t)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.profileWeight_pos`,
`«2610.05164v2».SineContinuum.sineJacobian_positive` with the arguments shown in the proof.
-/
theorem sineWeight_normalization (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    √(sineJacobian t)*√(2*(n:ℝ)+1)=√(π*((n:ℝ)+1/2))*«2606.16671v2».SineJacobi.profileWeight t := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.profileWeight_pos`,
  -- `«2610.05164v2».SineContinuum.sineJacobian_positive` with the arguments shown in the
  -- proof.
  have hs : 0 < sin (π*t) := (sqrt_pos.mp («2606.16671v2».SineJacobi.profileWeight_pos ht))
  have h₁ : 0 ≤ 2*(n:ℝ)+1 := by positivity
  have h₂ : 0 ≤ π*((n:ℝ)+1/2) := by positivity
  have hsq : (√(sineJacobian t)*√(2*(n:ℝ)+1))^2=
      (√(π*((n:ℝ)+1/2))*«2606.16671v2».SineJacobi.profileWeight t)^2 := by
    rw [mul_pow,mul_pow,sq_sqrt (sineJacobian_positive ht).le,sq_sqrt h₁,sq_sqrt h₂]
    rw [show «2606.16671v2».SineJacobi.profileWeight t^2=sin (π*t) from sq_sqrt hs.le]
    dsimp [sineJacobian]
    ring
  nlinarith [mul_nonneg (sqrt_nonneg (sineJacobian t)) (sqrt_nonneg (2*(n:ℝ)+1)),
    mul_nonneg (sqrt_nonneg (π*((n:ℝ)+1/2))) («2606.16671v2».SineJacobi.profileWeight_pos ht).le]

/--
The basis vectors have exactly the representatives printed in Lemma 5.

Exact identity `sineHilbertBasis n=ᵐ[volume] (fun t : LegendreInterval => upsilon n t)`.

Use: `«2610.05164v2».SineContinuum.greenOperator_basis` uses this identity to establish exact
identity `greenOperator (sineHilbertBasis n)=(mu n)⁻¹ • sineHilbertBasis n`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineHilbertBasis_ae (n : ℕ) : sineHilbertBasis n=ᵐ[volume]
    (fun t : LegendreInterval => upsilon n t) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hp := sineWeight.base_ac.ae_eq
    (sineCoordinate_measurePreserving.quasiMeasurePreserving.ae_eq_comp (normalizedLegendre_ae n))
  rw [sineHilbertBasis_apply,legendreHilbertBasis_apply]
  filter_upwards [sineUnitary_ae (normalizedLegendre n),hp,interval_interior_ae] with t hu hp ht
  simp only [Function.comp_def] at hp
  rw [hu,hp]
  rw [show (sineCoordinateEquiv t:ℝ)=sineCoordinate t from sineCoordinateIso_apply t,
    ← mul_assoc,sineWeight_normalization n ht]
  rfl

/--
The no-logarithm endpoint realization specified by the full diagonal basis domain, rather than
endpoint vanishing alone.

Use: `«2610.05164v2».SineContinuum.sineOperator_basis` uses this definition to establish exact
identity `sineOperator ⟨sineHilbertBasis n,sineOperator_basis_mem n⟩=mu n • sineHilbertBasis
n`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.
-/
def sineOperator : LegendreSpace →ₗ.[ℝ] LegendreSpace :=
  Continuum.unboundedDiagonalOperator sineHilbertBasis mu

/--
Equivalence of the displayed criteria: `u ∈ sineOperator.domain ↔ Summable (fun n : ℕ => (mu
n)^2*(sineHilbertBasis.repr u n)^2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.unboundedDiagonalDomain_iff` with
the arguments shown in the proof.
-/
theorem sineOperator_domain (u : LegendreSpace) :
    u ∈ sineOperator.domain ↔ Summable (fun n : ℕ => (mu n)^2*(sineHilbertBasis.repr u n)^2) :=
  Continuum.unboundedDiagonalDomain_iff _ _ _

/--
Membership in the specified domain/enclosure: `sineHilbertBasis n ∈ sineOperator.domain`.

Use: `«2610.05164v2».SineContinuum.sineOperator_basis` uses this assertion to establish exact
identity `sineOperator ⟨sineHilbertBasis n,sineOperator_basis_mem n⟩=mu n • sineHilbertBasis
n`.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.unboundedDiagonalDomain_basis`
with the arguments shown in the proof.
-/
theorem sineOperator_basis_mem (n : ℕ) : sineHilbertBasis n ∈ sineOperator.domain :=
  Continuum.unboundedDiagonalDomain_basis _ _ n

/--
Exact identity `sineOperator ⟨sineHilbertBasis n,sineOperator_basis_mem n⟩=mu n •
sineHilbertBasis n`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.unboundedDiagonalOperator_basis`
with the arguments shown in the proof.
-/
theorem sineOperator_basis (n : ℕ) :
    sineOperator ⟨sineHilbertBasis n,sineOperator_basis_mem n⟩=mu n • sineHilbertBasis n :=
  Continuum.unboundedDiagonalOperator_basis _ _ n

/--
Exact identity `sineOperator.adjoint=sineOperator`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.unboundedDiagonalOperator_selfAdjoint` with the arguments shown in
the proof.
-/
theorem sineOperator_selfAdjoint : sineOperator.adjoint=sineOperator :=
  Continuum.unboundedDiagonalOperator_selfAdjoint _ _

/--
The stated quantitative bound `0 ≤ inner ℝ (sineOperator u) (u:LegendreSpace)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.unboundedDiagonalOperator_nonnegative` with the arguments shown in
the proof.
-/
theorem sineOperator_nonnegative (u : sineOperator.domain) :
    0 ≤ inner ℝ (sineOperator u) (u:LegendreSpace) :=
  Continuum.unboundedDiagonalOperator_nonnegative _ _ (fun n => by unfold mu; positivity) u

end
end «2610.05164v2».SineContinuum
