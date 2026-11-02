import jacobi.Complex.FiniteResidues

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Use: parity_contour_residue_identity applies this theorem to the genuine sigma and tau sequences, with their proved exact pole counts.
-/
namespace jacobi.Complex
noncomputable section
open _root_.Complex Set Metric
set_option backward.isDefEq.respectTransparency false

/-- The actual finite residue formula preserves an increasing real spectral enumeration and sums precisely its first n original indices.
Use: parity_contour_residue_identity applies this theorem to the genuine sigma and tau sequences, with their proved exact pole counts.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the classical simple-pole residue theorem, proved in FiniteResidues.
Proof: use the actual image of Finset.range n as the finite pole set. Exhaustiveness identifies its zeros, the genuine pole counts exclude the boundary, and strict monotonicity ensures that the image sum has no duplicate indices. -/
theorem indexed_simple_residues (lambda : ℕ → ℝ) (hlambda : StrictMono lambda) (n : ℕ)
    {g h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0<R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hh : AnalyticOnNhd ℂ h (closedBall c R))
    (hzeros : ∀ z : ℂ,h z=0 ↔ ∃ k : ℕ,z=(lambda k:ℂ))
    (hsimple : ∀ k : ℕ,deriv h (lambda k:ℂ)≠0)
    (hopen : ∀ k : ℕ,(lambda k:ℂ)∈ball c R ↔ k<n)
    (hclosed : ∀ k : ℕ,(lambda k:ℂ)∈closedBall c R ↔ k<n) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ • (∮ z in C(c,R),g z/h z)=
      ∑ k∈Finset.range n,g (lambda k:ℂ)/deriv h (lambda k:ℂ) := by
  classical
  -- The pole set is constructed from the original enumeration, not chosen independently from its zero set.
  let S : Finset ℂ := (Finset.range n).image (fun k => (lambda k:ℂ))
  have hinside (p : ℂ) (hp : p∈S) : p∈ball c R := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hp
    exact (hopen k).mpr (Finset.mem_range.mp hk)
  have hzero (z : ℂ) (hz : z∈closedBall c R) : h z=0 ↔ z∈S := by
    constructor
    · intro h0
      obtain ⟨k,rfl⟩ := (hzeros z).mp h0
      exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr ((hclosed k).mp hz),rfl⟩
    · intro hm
      obtain ⟨k,_hk,rfl⟩ := Finset.mem_image.mp hm
      exact (hzeros _).mpr ⟨k,rfl⟩
  have hs (p : ℂ) (hp : p∈S) : deriv h p≠0 := by
    obtain ⟨k,_hk,rfl⟩ := Finset.mem_image.mp hp
    exact hsimple k
  have hr := finite_simple_residues S hR hg hh hinside hzero hs
  rw [show S=(Finset.range n).image (fun k => (lambda k:ℂ)) from rfl,
    Finset.sum_image (fun i _hi j _hj he => hlambda.injective (Complex.ofReal_injective he))] at hr
  exact hr

end
end jacobi.Complex
