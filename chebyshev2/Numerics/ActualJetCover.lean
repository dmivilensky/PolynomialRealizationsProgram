import chebyshev2.Numerics.JetArithmetic
import chebyshev2.Certificates.Partition

/-!
Article: chebyshev2, Lemma 20.
`chebyshev2.Numerics.actualJetCover_sound` combines checked local jets into an actual
full-interval quadrature cover.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.actualJetIntegralBox_sound_on`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
open Set chebyshev2.Certificates
set_option autoImplicit false

/--
An actual-function Taylor enclosure on one rational cell. The actual field proves validity
everywhere on that cell, making this an analytic enclosure rather than an unchecked proposal.

Use: `chebyshev2.Numerics.actualJetCover_sound` uses this record of data and proof
obligations to prove the quantified assertion `∀ x∈Icc (a:ℝ) b,∃
c∈cells,x∈Icc (c.domain.lo:ℝ) c.domain.hi ∧ JetEncloses c.jet f (Icc (c.domain.lo:ℝ)
c.domain.hi) x n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
structure ActualJetCell (f : ℝ → ℝ) (n : ℕ) where
  /-- Rational cell on which this actual-function jet is valid. -/
  domain : Cell
  /-- Interval Taylor jet proposed for the cell. -/
  jet : IntervalJet
  /-- Proof that the proposed jet encloses the derivatives of the actual function at every point of the closed cell. -/
  actual : ∀ x∈Icc (domain.lo:ℝ) domain.hi,JetEncloses jet f (Icc (domain.lo:ℝ) domain.hi) x n

 /--
Establishes the uniform, quantified assertion `∀ x∈Icc (a:ℝ) b,∃ c∈cells,x∈Icc (c.domain.lo:ℝ)
c.domain.hi ∧ JetEncloses c.jet f (Icc (c.domain.lo:ℝ) c.domain.hi) x n`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Use the identities/estimates `chebyshev2.Certificates.PartitionFrom.cover` with the
arguments shown in the proof.
-/
theorem actualJetCover_sound {f : ℝ → ℝ} {n : ℕ} (cells : List (ActualJetCell f n))
    {a b : ℚ} (h : PartitionFrom a b (cells.map ActualJetCell.domain)) (hab : a<b) :
    ∀ x∈Icc (a:ℝ) b,∃ c∈cells,x∈Icc (c.domain.lo:ℝ) c.domain.hi ∧
      JetEncloses c.jet f (Icc (c.domain.lo:ℝ) c.domain.hi) x n := by
  intro x hx
  obtain ⟨d,hd,hx⟩ := h.cover hab hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
  exact ⟨c,hc,hx,c.actual x hx⟩

end chebyshev2.Numerics
