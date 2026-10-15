import «2610.05164v2».SineContinuum.AffineLegendre

/-!
Article: 2610.05164v2, Lemma 5.
The exact definition H = pi² V (L+1/4) V⁻¹ on the complete article domain.
Result: `«2610.05164v2».SineContinuum.legendreV_operator` supplies the stated article conclusion.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency true

/--
The article's normalized basis of the literal Lebesgue space L²(-1,1).

Use: `«2610.05164v2».SineContinuum.affineLegendre_operator` uses this definition to establish
the precise assertion is `legendreOperator ⟨affineLegendreUnitary
(u:StandardSpace),(affineLegendre_domain _).mpr u.property⟩= affineLegendreUnitary
(standardLegendreOperator u)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.standardLegendreOperator_selfAdjoint`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.
-/
def standardLegendreHilbertBasis : HilbertBasis ℕ ℝ StandardSpace :=
  HilbertBasis.ofRepr (affineLegendreUnitary.trans legendreHilbertBasis.repr)

/--
Exact identity `standardLegendreHilbertBasis j=affineLegendreUnitary.symm (legendreHilbertBasis
j)`.

Use: `«2610.05164v2».SineContinuum.standardLegendreHilbertBasis_ae` rewrites with this identity
to establish the identity `standardLegendreHilbertBasis j=ᵐ[volume] (fun z : StandardInterval
=> √((j:ℝ)+1/2)*legendre j z)`.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem standardLegendreHilbertBasis_apply (j : ℕ) :
    standardLegendreHilbertBasis j=affineLegendreUnitary.symm (legendreHilbertBasis j) := rfl

/--
Exact identity `standardLegendreHilbertBasis j=ᵐ[volume] (fun z : StandardInterval =>
√((j:ℝ)+1/2)*legendre j z)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem standardLegendreHilbertBasis_ae (j : ℕ) : standardLegendreHilbertBasis j=ᵐ[volume]
    (fun z : StandardInterval => √((j:ℝ)+1/2)*legendre j z) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hp := standardWeight.base_ac.ae_eq
    ((affineLegendre_measurePreserving.symm affineLegendreEquiv).quasiMeasurePreserving.ae_eq_comp
      (normalizedLegendre_ae j))
  rw [standardLegendreHilbertBasis_apply,legendreHilbertBasis_apply]
  filter_upwards [affineLegendreUnitary_symm_ae (normalizedLegendre j),hp] with z hu hp
  simp only [Function.comp_def] at hp
  rw [hu,hp]
  change √(1/2:ℝ)*(√(2*(j:ℝ)+1)*(shifted j).eval ((1-(z:ℝ))/2))=_
  rw [← mul_assoc,← sqrt_mul (by norm_num : (0:ℝ)≤1/2)]
  have he : (1/2:ℝ)*(2*(j:ℝ)+1)=(j:ℝ)+1/2 := by ring
  rw [he]
  rfl

/--
Defines `standardLegendreOperator` of type `StandardSpace →ₗ.[ℝ] StandardSpace` by
`Continuum.unboundedDiagonalOperator standardLegendreHilbertBasis (fun j => (j:ℝ)*(j+1))`.

Use: `«2610.05164v2».SineContinuum.affineLegendre_operator` uses this definition to establish
the precise assertion is `legendreOperator ⟨affineLegendreUnitary
(u:StandardSpace),(affineLegendre_domain _).mpr u.property⟩= affineLegendreUnitary
(standardLegendreOperator u)`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.
-/
def standardLegendreOperator : StandardSpace →ₗ.[ℝ] StandardSpace :=
  Continuum.unboundedDiagonalOperator standardLegendreHilbertBasis (fun j => (j:ℝ)*(j+1))

/--
Equivalence of the displayed criteria: `u ∈ standardLegendreOperator.domain ↔ Summable (fun j :
ℕ => (j:ℝ)^2*((j:ℝ)+1)^2*(standardLegendreHilbertBasis.repr u j)^2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.unboundedDiagonalDomain_iff` with
the arguments shown in the proof.
-/
theorem standardLegendreOperator_domain (u : StandardSpace) :
    u ∈ standardLegendreOperator.domain ↔ Summable
      (fun j : ℕ => (j:ℝ)^2*((j:ℝ)+1)^2*(standardLegendreHilbertBasis.repr u j)^2) := by
  change u ∈ Continuum.unboundedDiagonalDomain standardLegendreHilbertBasis
    (fun j => (j:ℝ)*(j+1)) ↔ _
  simpa only [mul_pow,mul_assoc] using
    Continuum.unboundedDiagonalDomain_iff standardLegendreHilbertBasis (fun j => (j:ℝ)*(j+1)) u

/--
Exact identity `standardLegendreOperator.adjoint=standardLegendreOperator`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.unboundedDiagonalOperator_selfAdjoint` with the arguments shown in
the proof.
-/
theorem standardLegendreOperator_selfAdjoint :
    standardLegendreOperator.adjoint=standardLegendreOperator :=
  Continuum.unboundedDiagonalOperator_selfAdjoint _ _

/--
Exact identity `legendreHilbertBasis.repr (affineLegendreUnitary
u)=standardLegendreHilbertBasis.repr u`.

Use: `«2610.05164v2».SineContinuum.affineLegendre_symm_repr` rewrites with this identity to
establish exact identity `standardLegendreHilbertBasis.repr (affineLegendreUnitary.symm
u)=legendreHilbertBasis.repr u`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem affineLegendre_repr (u : StandardSpace) :
    legendreHilbertBasis.repr (affineLegendreUnitary u)=standardLegendreHilbertBasis.repr u := rfl

/--
Exact identity `standardLegendreHilbertBasis.repr (affineLegendreUnitary.symm
u)=legendreHilbertBasis.repr u`.

Use: `«2610.05164v2».SineContinuum.affineLegendre_domain` uses this identity to establish
equivalence of the displayed criteria: `affineLegendreUnitary u ∈ legendreOperator.domain ↔ u ∈
standardLegendreOperator.domain`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.affineLegendre_repr` with the
arguments shown in the proof.
-/
theorem affineLegendre_symm_repr (u : LegendreSpace) :
    standardLegendreHilbertBasis.repr (affineLegendreUnitary.symm u)=legendreHilbertBasis.repr u := by rw [← affineLegendre_repr,affineLegendreUnitary.apply_symm_apply]

/--
Equivalence of the displayed criteria: `affineLegendreUnitary u ∈ legendreOperator.domain ↔ u ∈
standardLegendreOperator.domain`.

Use: `«2610.05164v2».SineContinuum.legendreV_domain` uses this assertion to establish
equivalence of the displayed criteria: `legendreV u ∈ sineOperator.domain ↔ u ∈
standardLegendreOperator.domain`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.affineLegendre_symm_repr`
with the arguments shown in the proof.
-/
theorem affineLegendre_domain (u : StandardSpace) :
    affineLegendreUnitary u ∈ legendreOperator.domain ↔ u ∈ standardLegendreOperator.domain := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.affineLegendre_symm_repr` with
  -- the arguments shown in the proof.
  change (∃ v, Continuum.UnboundedDiagonalGraph legendreHilbertBasis
    (fun j => (j:ℝ)*(j+1)) (affineLegendreUnitary u) v) ↔ _
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨affineLegendreUnitary.symm v,?_⟩
    intro j
    simpa only [affineLegendre_repr,affineLegendre_symm_repr] using hv j
  · rintro ⟨v,hv⟩
    refine ⟨affineLegendreUnitary v,?_⟩
    intro j
    simpa only [affineLegendre_repr] using hv j

/--
The precise assertion is `legendreOperator ⟨affineLegendreUnitary
(u:StandardSpace),(affineLegendre_domain _).mpr u.property⟩= affineLegendreUnitary
(standardLegendreOperator u)`.

Use: `«2610.05164v2».SineContinuum.legendreV_operator` rewrites with this identity to establish
the precise assertion is `sineOperator ⟨legendreV (u:StandardSpace),(legendreV_domain _).mpr
u.property⟩= π^2 • legendreV (standardLegendreOperator u+(1/4:ℝ) • (u:StandardSpace))`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_operator`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.UnboundedDiagonalGraph.unique`,
`«2610.05164v2».Continuum.unboundedDiagonalOperator_graph` with the arguments shown in the
proof.
-/
theorem affineLegendre_operator (u : standardLegendreOperator.domain) :
    legendreOperator ⟨affineLegendreUnitary (u:StandardSpace),(affineLegendre_domain _).mpr u.property⟩=
      affineLegendreUnitary (standardLegendreOperator u) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.UnboundedDiagonalGraph.unique`,
  -- `«2610.05164v2».Continuum.unboundedDiagonalOperator_graph` with the arguments shown in the
  -- proof.
  apply Continuum.UnboundedDiagonalGraph.unique (Continuum.unboundedDiagonalOperator_graph _ _ _)
  intro j
  have h := Continuum.unboundedDiagonalOperator_graph standardLegendreHilbertBasis
    (fun j => (j:ℝ)*(j+1)) u j
  change standardLegendreHilbertBasis.repr (standardLegendreOperator u) j=
    (j:ℝ)*(j+1)*standardLegendreHilbertBasis.repr (u:StandardSpace) j at h
  simpa only [affineLegendre_repr] using h

/--
The article's actual unitary V from L²(-1,1) to L²(0,1).

Use: `«2610.05164v2».SineContinuum.legendreV_operator` uses this definition to establish the
precise assertion is `sineOperator ⟨legendreV (u:StandardSpace),(legendreV_domain _).mpr
u.property⟩= π^2 • legendreV (standardLegendreOperator u+(1/4:ℝ) • (u:StandardSpace))`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.
-/
def legendreV : StandardSpace ≃ₗᵢ[ℝ] LegendreSpace := affineLegendreUnitary.trans sineUnitary

/--
Defines `cosineInterval` of type `StandardInterval` by `⟨cos (π*(t:ℝ)),⟨neg_one_le_cos
_,cos_le_one _⟩⟩`.

Use: `«2610.05164v2».SineContinuum.legendreV_ae` uses this definition to establish exact
identity `legendreV f=ᵐ[volume] (fun t : LegendreInterval => √(π*sin (π*(t:ℝ)))*f
(cosineInterval t))`.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.
-/
def cosineInterval (t : LegendreInterval) : StandardInterval :=
  ⟨cos (π*(t:ℝ)),⟨neg_one_le_cos _,cos_le_one _⟩⟩

/--
Exact identity `legendreV f=ᵐ[volume] (fun t : LegendreInterval => √(π*sin (π*(t:ℝ)))*f
(cosineInterval t))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem legendreV_ae (f : StandardSpace) : legendreV f=ᵐ[volume]
    (fun t : LegendreInterval => √(π*sin (π*(t:ℝ)))*f (cosineInterval t)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hf := sineWeight.base_ac.ae_eq
    (sineCoordinate_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (affineLegendreUnitary_ae f))
  filter_upwards [sineUnitary_ae (affineLegendreUnitary f),hf,interval_interior_ae] with t hu hf ht
  change sineUnitary (affineLegendreUnitary f) t=_
  simp only [Function.comp_def] at hf
  rw [hu,hf]
  have he : affineLegendreEquiv (sineCoordinateEquiv t)=cosineInterval t := by
    apply Subtype.ext
    change 1-2*(sineCoordinateEquiv t:ℝ)=cos (π*(t:ℝ))
    have hc : (sineCoordinateEquiv t:ℝ)=sineCoordinate t := sineCoordinateIso_apply t
    rw [hc]
    unfold sineCoordinate
    ring
  rw [he]
  have hn : √(sineJacobian t)/√(1/2:ℝ)=√(π*sin (π*(t:ℝ))) := by
    rw [← sqrt_div (sineJacobian_nonnegative t.property)]
    congr 1
    unfold sineJacobian
    ring
  calc
    _ = (√(sineJacobian t)/√(1/2:ℝ))*f (cosineInterval t) := by ring
    _ = _ := by rw [hn]

/--
Equivalence of the displayed criteria: `legendreV u ∈ sineOperator.domain ↔ u ∈
standardLegendreOperator.domain`.

Use: `«2610.05164v2».SineContinuum.legendreV_operator` uses this assertion to establish the
precise assertion is `sineOperator ⟨legendreV (u:StandardSpace),(legendreV_domain _).mpr
u.property⟩= π^2 • legendreV (standardLegendreOperator u+(1/4:ℝ) • (u:StandardSpace))`.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.sineUnitary_domain_iff`,
`«2610.05164v2».SineContinuum.affineLegendre_domain` with the arguments shown in the proof.
-/
theorem legendreV_domain (u : StandardSpace) :
    legendreV u ∈ sineOperator.domain ↔ u ∈ standardLegendreOperator.domain :=
  (sineUnitary_domain_iff (affineLegendreUnitary u)).trans (affineLegendre_domain u)

/--
The exact definition H = pi² V (L+1/4) V⁻¹ on the complete article domain.

The precise assertion is `sineOperator ⟨legendreV (u:StandardSpace),(legendreV_domain _).mpr
u.property⟩= π^2 • legendreV (standardLegendreOperator u+(1/4:ℝ) • (u:StandardSpace))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 5.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — self-adjoint Legendre
realization.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.affineLegendre_domain`,
`«2610.05164v2».SineContinuum.sineOperator_conjugacy`,
`«2610.05164v2».SineContinuum.affineLegendre_operator` with the arguments shown in the proof.
-/
theorem legendreV_operator (u : standardLegendreOperator.domain) :
    sineOperator ⟨legendreV (u:StandardSpace),(legendreV_domain _).mpr u.property⟩=
      π^2 • legendreV (standardLegendreOperator u+(1/4:ℝ) • (u:StandardSpace)) := by
  have h := sineOperator_conjugacy
    (⟨affineLegendreUnitary (u:StandardSpace),(affineLegendre_domain _).mpr u.property⟩ : legendreOperator.domain)
  rw [affineLegendre_operator] at h
  simpa only [legendreV,LinearIsometryEquiv.trans_apply,map_add,map_smul] using h

end
end «2610.05164v2».SineContinuum
