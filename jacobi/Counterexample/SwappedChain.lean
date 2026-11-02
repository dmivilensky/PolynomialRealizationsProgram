import jacobi.Counterexample.SwappedEntries
import jacobi.Finite.AlternatingConjugation

/-!
Article: jacobi, Proposition 6.1.
The source's attaining matrix is constructed as an actual finite Jacobi
chain from the unchanged swapped Gram matrix. Its original couplings
are positive, and its resolvent pencil is exactly the printed positive
affine alternating conjugation of B^T*B.
Use: constantDriftChain applies the source's affine alternating conjugation to this unchanged swapped matrix.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix jacobi.Finite chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The actual positive-coupling Jacobi encoding of the original Cholesky swap.
Use: constantDriftChain applies the source's affine alternating conjugation to this unchanged swapped matrix.
Article: jacobi, Proposition 6.1.
-/
def swappedJacobi (d l:ℕ→ℝ) (N:ℕ) : Jacobi N := fromMatrix (swappedGram d l N)

/-- The actual Jacobi encoding recovers the complete original swapped matrix under the stated source factor signs and positive drift.
Use: constantDriftChain_pencil computes the actual attaining matrix inverse from the independently proved original swapped inverse.
Article: jacobi, Proposition 6.1.
Proof: the original swap is positive definite, hence symmetric. Its
proved exact adjacent entries are positive products, and every other
off-band entry is zero. The earlier general matrix encoding therefore
recovers precisely the original matrix. -/
theorem swappedJacobi_matrix {N:ℕ} (d l:ℕ→ℝ) {kappa:ℝ}
    (hk:0<kappa) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    (swappedJacobi d l N).matrix=swappedGram d l N := by
  -- Both the signs and the complete finite band structure concern the actual swapped matrix.
  apply fromMatrix_eq _ (swapped_posDef d l hk hd).isHermitian
  · intro i j hij
    have hne : i≠j := by intro h; have hv:=congrArg Fin.val h; omega
    rw [swapped_entry,ite_eq_right hne,ite_eq_left hij]
    exact (mul_pos (hlower j (by omega) j.isLt) (hdiag j j.isLt)).le
  · intro i j hfar
    have hne : i≠j := by intro h; have hv:=congrArg Fin.val h; rcases hfar with h | h <;> omega
    have hu : ¬i.val+1=j.val := by rcases hfar with h | h <;> omega
    have hl : ¬j.val+1=i.val := by rcases hfar with h | h <;> omega
    simp only [swapped_entry,hne,hu,hl,ite_false]

/-- The actual swapped Jacobi chain is irreducible when the original lower factor has positive interior entries.
Use: constantDriftChain_irreducible places the explicit attaining chain in its full original positive-coupling fibre.
Article: jacobi, Proposition 6.1.
Proof: each genuine squared Jacobi coupling is the square of the
proved actual neighboring product l_i*d_i, which is strictly positive. -/
theorem swappedJacobi_irreducible {N:ℕ} (d l:ℕ→ℝ)
    (hdiag:∀i<N,0<d i) (hlower:∀ i, 0 < i → i < N → 0 < l i) :
    (swappedJacobi d l N).Irreducible := by
  -- The canonical unused and tail coefficients remain the original zero extension.
  intro i hi hiN
  change (if h : 0 < i ∧ i < N then
    (swappedGram d l N ⟨i-1,by omega⟩ ⟨i,h.2⟩)^2 else 0)>0
  rw [dite_eq_left ⟨hi,hiN⟩,swapped_entry]
  have hne : (⟨i-1,by omega⟩:Fin N)≠⟨i,hiN⟩ := by
    intro h; have hv:=congrArg Fin.val h; dsimp only at hv; omega
  simp only [hne,ite_false,show i-1+1=i by omega,ite_true]
  exact sq_pos_of_pos (mul_pos (hlower i hi hiN) (hdiag i hiN))

/-- The source's explicit attaining Jacobi chain, with its exact positive-coupling finite representation.
Use: constantDriftChain_green and constantDriftChain_minimum prove its original constant resolvent diagonal and full-fibre optimality.
Article: jacobi, Proposition 6.1.
-/
def constantDriftChain (d l:ℕ→ℝ) (N:ℕ) (H:ℝ) : Jacobi N :=
  affine (reflect (swappedJacobi d l N)) H⁻¹ 1

/-- The constructed original attaining chain has positive couplings for every positive source scale.
Use: constantDriftChain_minimum supplies an actual original fibre member attaining the lower bound.
Article: jacobi, Proposition 6.1.
Proof: both the original spectral reflection and the positive affine rescaling preserve the already proved original irreducibility. -/
theorem constantDriftChain_irreducible {N:ℕ} (d l:ℕ→ℝ) {H:ℝ} (hH:0<H)
    (hdiag:∀i<N,0<d i) (hlower:∀ i, 0 < i → i < N → 0 < l i) :
    (constantDriftChain d l N H).Irreducible :=
  affine_irreducible (affine_irreducible (swappedJacobi_irreducible d l hdiag hlower)
    (by norm_num : (-1:ℝ)≠0) 0) (inv_ne_zero hH.ne') 1

/-- The actual attaining Jacobi chain has exactly the original affine alternating-conjugation resolvent pencil.
Use: constantDriftChain_green identifies its true inverse, preserving the original H and kappa normalizations.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the actual Jacobi reflection is -D*Y'*D. The actual positive
affine map multiplies it by H^(-1) and adds I. Subtraction cancels that
identity matrix exactly. -/
theorem constantDriftChain_pencil {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    1-(constantDriftChain d l N H).matrix=
      H⁻¹ • (alternatingMatrix N*swappedGram d l N*alternatingMatrix N) := by
  -- The equality is for the literal matrix whose inverse defines the source finite energy.
  rw [constantDriftChain,affine_matrix _ (inv_nonneg.mpr hH.le) 1,reflect_matrix,
    swappedJacobi_matrix d l hk hdiag hlower hd]
  have hone : Matrix.scalar (Fin N) (1:ℝ)=1 := by ext i j; simp
  rw [hone,smul_neg]
  module

end
end jacobi.Counterexample
