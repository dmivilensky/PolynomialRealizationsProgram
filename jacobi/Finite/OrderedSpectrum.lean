import jacobi.Finite.Endpoint
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Finset.Sort

/-!
Article: jacobi, Proposition 6.1.
Every actual irreducible Jacobi matrix has a simple spectrum, even
before any spectral window is prescribed. The endpoint cofactor from
chebyshev1 excludes repeated eigenvalues. The community finite sorting
construction then supplies an increasing exhaustive enumeration.
Source: the finite spectral theorem and the Jacobi endpoint cofactor.
Use: basis_values_injective and increasingSpectrum construct the complete actual simple ordered spectrum without assuming distinct prescribed nodes.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Polynomial Set chebyshev1 chebyshev2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual derivative of an irreducible finite Jacobi characteristic polynomial is nonzero at every spectral value.
Use: basis_values_injective and increasingSpectrum construct the complete actual simple ordered spectrum without assuming distinct prescribed nodes.
Article: jacobi, Proposition 6.1.
Proof: the genuine endpoint cofactor is the strictly positive product
of all actual internal couplings. Its spectral expression contains
the characteristic derivative as a factor, so that derivative cannot vanish. -/
theorem charpoly_derivative_ne_spectrum {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible)
    {x:ℝ} (hx:x∈spectrum ℝ J.matrix) : J.matrix.charpoly.derivative.eval x≠0 := by
  -- The endpoint cofactor identity itself does not require spectral simplicity.
  cases N with
  | zero =>
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hx
    simp only [Matrix.charpoly_isEmpty,Polynomial.IsRoot,eval_one,one_ne_zero] at hx
  | succ n =>
    let B:=SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
    rw [J.matrix_isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨k,rfl⟩:=hx
    have he:=spectral_endpoint_signed J B k
    have hp:0<∏i:Fin n,Real.sqrt (J.data.aSq (i.val+1)) :=
      Finset.prod_pos (fun i _=>Real.sqrt_pos.mpr (hJ (i.val+1) (by omega) (by omega)))
    intro hz
    have hz':J.matrix.charpoly.derivative.eval (B.eigenvalues k)=0:=hz
    rw [hz',mul_zero] at he
    exact hp.ne' he.symm

/-- Every actual spectral basis of an irreducible finite Jacobi matrix has distinct genuine eigenvalues.
Use: increasingSpectrum sorts exactly N different original nodes, rather than silently discarding multiplicities.
Article: jacobi, Proposition 6.1.
Proof: if two spectral columns had the same eigenvalue, the exact
characteristic derivative product would contain a zero factor. The
proved endpoint cofactor forbids this at every actual spectral value. -/
theorem basis_values_injective {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible)
    (B:SpectralBasis J.matrix) : Function.Injective B.eigenvalues := by
  classical
  -- The complete original matrix polynomial, not a chosen square-free replacement, is differentiated.
  intro i j hij
  by_contra hne
  have hs:B.eigenvalues i∈spectrum ℝ J.matrix := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,B.charpoly_factor]
    change (∏k:Fin N,(X-C (B.eigenvalues k))).eval (B.eigenvalues i)=0
    rw [eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hd:=charpoly_derivative_ne_spectrum J hJ hs
  apply hd
  rw [B.charpoly_derivative]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne,Finset.mem_univ j⟩)
    (by rw [hij,sub_self])

/-- The original increasing finite spectrum of an arbitrary genuine irreducible Jacobi matrix.
Use: the Laguerre ordered-zero limit uses the actual matrix nodes with every multiplicity discharged by basis_values_injective.
Article: jacobi, Proposition 6.1.
-/
def increasingSpectrum {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible) : Fin N ↪o ℝ := by
  classical
  let B:=SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
  let S:=Finset.univ.image B.eigenvalues
  have hcard:S.card=N := by
    rw [Finset.card_image_of_injective _ (basis_values_injective J hJ B),
      Finset.card_univ,Fintype.card_fin]
  exact S.orderEmbOfFin hcard

/-- The original increasing finite spectrum enumerates exactly every genuine matrix spectral value.
Use: actual Laguerre roots and locally transferred zeros have a unique finite source index.
Article: jacobi, Proposition 6.1.
Proof: the sorted community embedding has exactly the original image
of the actual spectral basis as its range. The finite Hermitian spectral
theorem identifies that image with the original matrix spectrum. -/
theorem increasingSpectrum_exhaustive {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible) (x:ℝ) :
    x∈spectrum ℝ J.matrix ↔ ∃i:Fin N,increasingSpectrum J hJ i=x := by
  classical
  -- Sorting only relabels the original complete finite spectrum.
  rw [J.matrix_isHermitian.spectrum_real_eq_range_eigenvalues]
  change (∃i:Fin N,J.matrix_isHermitian.eigenvalues i=x) ↔
    x∈range (increasingSpectrum J hJ)
  rw [increasingSpectrum,Finset.range_orderEmbOfFin]
  simp only [Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and,SpectralBasis.ofHermitian]

/-- Every genuinely enumerated increasing spectral value belongs to the actual original matrix spectrum.
Use: supplies the original Laguerre zero equation and positivity at each canonical finite index.
Article: jacobi, Proposition 6.1.
Proof: specialize the proved exhaustive enumeration to its own index. -/
theorem increasingSpectrum_mem {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible) (i:Fin N) :
    increasingSpectrum J hJ i∈spectrum ℝ J.matrix :=
  (increasingSpectrum_exhaustive J hJ _).mpr ⟨i,rfl⟩

/-- An actual spectral basis can be relabelled to the genuine increasing complete spectrum.
Use: increasingSpectrum_inverse_trace sums the original inverse eigenvalues with the canonical finite ordering.
Article: jacobi, Proposition 6.1.
Source: the finite spectral theorem under a permutation of its columns.
Proof: choose the original spectral column at each sorted value.
Distinct sorted values make this a finite permutation, and the existing
spectral-basis relabelling preserves both orthogonality identities. -/
theorem exists_increasing_basis {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible) :
    ∃B:SpectralBasis J.matrix,B.eigenvalues=increasingSpectrum J hJ := by
  -- Only spectral labels change; every physical matrix entry is retained.
  let B:=SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
  have hex (k:Fin N) : ∃i:Fin N,B.eigenvalues i=increasingSpectrum J hJ k := by
    have hm:=increasingSpectrum_mem J hJ k
    rw [J.matrix_isHermitian.spectrum_real_eq_range_eigenvalues] at hm
    exact hm
  let f:Fin N→Fin N:=fun k=>Classical.choose (hex k)
  have hf (k:Fin N) : B.eigenvalues (f k)=increasingSpectrum J hJ k:=Classical.choose_spec (hex k)
  have hinj:Function.Injective f := by
    intro i j hij
    apply (increasingSpectrum J hJ).injective
    rw [← hf i,← hf j,hij]
  let e:=Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨relabelBasis B e,funext hf⟩

/-- The actual inverse trace equals the full sum of reciprocal original increasing eigenvalues whenever the original matrix is nonsingular.
Use: the Laguerre l1 edge limit combines this exact identity with its independently proved constant-drift inverse trace.
Article: jacobi, Proposition 6.1.
Source: the finite spectral theorem and trace invariance under orthogonal conjugation, reused from chebyshev2.
Proof: relabel an actual spectral basis to the genuine sorted nodes.
The proved coordinate-inverse identity reduces the true nonsingular
matrix inverse to the diagonal of actual nonzero reciprocal eigenvalues. -/
theorem increasingSpectrum_inverse_trace {N:ℕ} (J:Jacobi N) (hJ:J.Irreducible)
    (h0:∀i,increasingSpectrum J hJ i≠0) :
    J.matrix⁻¹.trace=∑i:Fin N,1/increasingSpectrum J hJ i := by
  classical
  -- Invertibility is discharged at every actual spectral entry before diagonal inversion.
  obtain ⟨B,hB⟩:=exists_increasing_basis J hJ
  have hb:∀i,B.eigenvalues i≠0:=by intro i; rw [hB]; exact h0 i
  have hd:(diagonal B.eigenvalues)⁻¹=diagonal (fun i=>1/B.eigenvalues i) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal_apply,Matrix.one_apply,hb]
  rw [← chebyshev2.SpectralCoordinates.coordinates_trace B,
    chebyshev2.SpectralCoordinates.coordinates_inv,
    show B.coordinates J.matrix=diagonal B.eigenvalues from B.diagonalize,hd,Matrix.trace_diagonal,hB]

end
end jacobi.Finite
