import chebyshev2.SineContinuum.GreenOperator

/-!
Article: chebyshev2, Lemma 5.
Lemma 5: the continuous Green integral really is the full inverse of the no-logarithm self-adjoint
realization.
Result: `chebyshev2.SineContinuum.sineOperator_domain_eq_range` supplies the stated article
conclusion.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency true

/--
The precise assertion is `sineHilbertBasis.repr (greenOperator f) n= (mu
n)⁻¹*sineHilbertBasis.repr f n`.

Use: `chebyshev2.SineContinuum.greenOperator_mem_domain` rewrites with this identity to
establish membership in the specified domain/enclosure: `greenOperator f ∈
sineOperator.domain`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.sineOperator_domain_eq_range`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.greenOperator_positive`,
`chebyshev2.SineContinuum.greenOperator_basis` with the arguments shown in the proof.
-/
theorem greenOperator_repr (f : LegendreSpace) (n : ℕ) :
    sineHilbertBasis.repr (greenOperator f) n=
      (mu n)⁻¹*sineHilbertBasis.repr f n := by
  simp only [sineHilbertBasis.repr_apply_apply]
  have h := greenOperator_positive.1 (sineHilbertBasis n) f
  change inner ℝ (greenOperator (sineHilbertBasis n)) f=
    inner ℝ (sineHilbertBasis n) (greenOperator f) at h
  rw [← h,greenOperator_basis,real_inner_smul_left]

/--
Membership in the specified domain/enclosure: `greenOperator f ∈ sineOperator.domain`.

Use: `chebyshev2.SineContinuum.sineOperator_domain_eq_range` uses this assertion to
establish exact identity `(sineOperator.domain : Set LegendreSpace)=Set.range greenOperator`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.sineOperator_domain_eq_range`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.greenOperator_repr`,
`chebyshev2.SineContinuum.mu_positive` with the arguments shown in the proof.
-/
theorem greenOperator_mem_domain (f : LegendreSpace) : greenOperator f ∈ sineOperator.domain := by
  refine ⟨f,?_⟩
  intro n
  rw [greenOperator_repr,← mul_assoc,mul_inv_cancel₀ (mu_positive n).ne',one_mul]

/--
Lemma 5: the continuous Green integral really is the full inverse of the no-logarithm
self-adjoint realization.

Exact identity `sineOperator ⟨greenOperator f,greenOperator_mem_domain f⟩=f`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 5.

Proof: Use the identities/estimates `chebyshev2.Continuum.UnboundedDiagonalGraph.unique`,
`chebyshev2.Continuum.unboundedDiagonalOperator_graph`,
`chebyshev2.SineContinuum.greenOperator_repr` with the arguments shown in the proof.
-/
theorem sineOperator_greenOperator (f : LegendreSpace) :
    sineOperator ⟨greenOperator f,greenOperator_mem_domain f⟩=f := by
  apply Continuum.UnboundedDiagonalGraph.unique
    (Continuum.unboundedDiagonalOperator_graph sineHilbertBasis mu _)
  intro n
  rw [greenOperator_repr,← mul_assoc,mul_inv_cancel₀ (mu_positive n).ne',one_mul]

/--
Exact identity `greenOperator (sineOperator u)=(u:LegendreSpace)`.

Use: `chebyshev2.SineContinuum.sineOperator_domain_eq_range` uses this identity to
establish exact identity `(sineOperator.domain : Set LegendreSpace)=Set.range greenOperator`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.sineOperator_domain_eq_range`.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalOperator_graph`,
`chebyshev2.SineContinuum.greenOperator_repr`, `chebyshev2.SineContinuum.mu_positive`
with the arguments shown in the proof.
-/
theorem greenOperator_sineOperator (u : sineOperator.domain) :
    greenOperator (sineOperator u)=(u:LegendreSpace) := by
  apply sineHilbertBasis.repr.injective
  ext n
  have h := Continuum.unboundedDiagonalOperator_graph sineHilbertBasis mu u n
  change sineHilbertBasis.repr (sineOperator u) n=mu n*sineHilbertBasis.repr (u:LegendreSpace) n at h
  rw [greenOperator_repr,h,← mul_assoc,inv_mul_cancel₀ (mu_positive n).ne',one_mul]

/--
Exact identity `(sineOperator.domain : Set LegendreSpace)=Set.range greenOperator`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 5.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.greenOperator_sineOperator`,
`chebyshev2.SineContinuum.greenOperator_mem_domain` with the arguments shown in the proof.
-/
theorem sineOperator_domain_eq_range :
    (sineOperator.domain : Set LegendreSpace)=Set.range greenOperator := by
  ext f
  constructor
  · intro hf
    exact ⟨sineOperator ⟨f,hf⟩,greenOperator_sineOperator ⟨f,hf⟩⟩
  · rintro ⟨g,rfl⟩
    exact greenOperator_mem_domain g

end
end chebyshev2.SineContinuum
