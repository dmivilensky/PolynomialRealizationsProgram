import bezout.Models.Cycle
import Mathlib.Analysis.Fourier.ZMod

/-!
Article: bezout, complete active cycle spectrum in the network model.
Use: the cyclic character modes exhaust the finite spectrum, including
multiplicities; an invertible Fourier map diagonalizes the actual Laplacian.
Proof: exact character shift identities and the finite Fourier inversion equivalence.
-/

namespace bezout.Models.Network
noncomputable section
open scoped BigOperators
variable (m : ℕ) [NeZero m]

/-- Complex extension of the same actual nearest-neighbor cyclic Laplacian. -/
def complexCycle : (ZMod m → ℂ) →ₗ[ℂ] (ZMod m → ℂ) where
  toFun u i := 2*u i-u (i+1)-u (i-1)
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c u := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The full complex cyclic mode, whose real part is the real cosine eigenmode. -/
def complexMode (j i : ZMod m) : ℂ := ZMod.stdAddChar (j*i)

/-- Exact complex mode action with the real eigenvalue from the manuscript. -/
theorem complex_mode_eigenvector (j : ZMod m) :
    complexCycle m (complexMode m j)=(cycleEigenvalue m j:ℂ) • complexMode m j := by
  funext i
  have hp : j*(i+1)=j*i+j := by ring
  have hm : j*(i-1)=j*i+(-j) := by ring
  change 2*ZMod.stdAddChar (j*i)-ZMod.stdAddChar (j*(i+1))-
    ZMod.stdAddChar (j*(i-1))=(cycleEigenvalue m j:ℂ)*ZMod.stdAddChar (j*i)
  rw [hp, hm, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, character_neg]
  simp only [cycleEigenvalue, ← character_real m j, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im] <;> norm_num <;> ring

/-- The Fourier reconstruction map is an actual linear equivalence. -/
def cycleSynthesis : (ZMod m → ℂ) ≃ₗ[ℂ] (ZMod m → ℂ) :=
  (ZMod.dft : (ZMod m → ℂ) ≃ₗ[ℂ] (ZMod m → ℂ)).symm

/-- Fourier reconstruction is a complete linear combination of the cyclic modes. -/
theorem cycleSynthesis_expansion (c : ZMod m → ℂ) :
    cycleSynthesis m c=(m:ℂ)⁻¹ • ∑ j, c j • complexMode m j := by
  funext i
  rw [cycleSynthesis, ZMod.invDFT_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, complexMode, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The complete Fourier equivalence diagonalizes the literal cyclic Laplacian. -/
theorem cycle_diagonalization (c : ZMod m → ℂ) :
    complexCycle m (cycleSynthesis m c)=
      cycleSynthesis m (fun j => (cycleEigenvalue m j:ℂ)*c j) := by
  rw [cycleSynthesis_expansion, cycleSynthesis_expansion, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, complex_mode_eigenvector]
  simp only [smul_smul, mul_comm]

end
end bezout.Models.Network
