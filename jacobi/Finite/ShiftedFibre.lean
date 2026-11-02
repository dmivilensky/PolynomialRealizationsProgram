import jacobi.Finite.AffineSpectrum
import jacobi.Finite.OrderedBasis
import jacobi.Finite.GreenEntries

/-!
Article: jacobi, Corollary C.6.
The affine contraction acts on every matrix of the original fibre. Its
Green matrix is exactly the original shifted inverse multiplied by theta.
This is the finite algebraic input to the shifted Transfer argument.
Use: shiftScale and shiftedNodes keep both spectral endpoints in (-1,1).
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix chebyshev1 chebyshev2

/-- The source's nonnegative translation before contracting a shifted fibre.
Use: shiftScale and shiftedNodes keep both spectral endpoints in (-1,1).
Article: jacobi, Theorem C.5.
-/
def shiftTranslation (z:ℝ) : ℝ := max (1-z) 0/2

/-- The source's positive affine normalization at a real resolvent point.
Use: shiftedFibre_matrix and shiftedFibre_green identify the genuine transformed inverse.
Article: jacobi, Theorem C.5.
-/
def shiftScale (z:ℝ) : ℝ := z+shiftTranslation z

/-- A positive real resolvent point gives a positive original affine scale.
Use: shiftedNodes and shiftedFibre preserve strict node order and positive couplings.
Article: jacobi, Theorem C.5.
Proof: the translation is nonnegative. -/
theorem shiftScale_pos {z:ℝ} (hz:0<z) : 0<shiftScale z := by
  have : 0≤shiftTranslation z := div_nonneg (le_max_right _ _) (by norm_num)
  exact add_pos_of_pos_of_nonneg hz this

/-- The actual affine image of every original prescribed node lies in (-1,1).
Use: shiftedFibre_inFiber puts every original competitor in a contractive fibre.
Article: jacobi, Theorem C.5.
Proof: the upper endpoint is the genuine positive shifted spectral gap;
the lower endpoint follows from z+2c' >= 1 and the original node > -1. -/
def shiftedNodes {N:ℕ} (S:Nodes N) (z:ℝ) (hz:0<z) (ht:∀k,S.value k<z) : Nodes N where
  value k := (S.value k+shiftTranslation z)/shiftScale z
  strictAnti := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right (shiftScale_pos hz)).mpr (by linarith [S.strictAnti hij])
  interval k := by
    have hc : 1-z≤2*shiftTranslation z := by
      unfold shiftTranslation
      linarith [le_max_left (1-z) 0]
    constructor
    · apply (lt_div_iff₀ (shiftScale_pos hz)).mpr
      dsimp only [shiftScale]
      linarith [(S.interval k).1]
    · exact (div_lt_one (shiftScale_pos hz)).mpr (by dsimp only [shiftScale]; linarith [ht k])

/-- The actual original affine map on arbitrary finite Jacobi competitors.
Use: the shifted lower bound uses all original matrices, without a symmetry restriction.
Article: jacobi, Theorem C.5.
-/
def shiftedFibre {N:ℕ} (J:Jacobi N) (z:ℝ) : Jacobi N :=
  affine J (shiftScale z)⁻¹ (shiftTranslation z/shiftScale z)

/-- Every original fibre competitor maps to the source's transformed contractive fibre.
Use: the real-shift Transfer lower bound compares full original infima.
Article: jacobi, Theorem C.5.
Proof: positive scaling preserves irreducibility. The original ordered
spectral basis is unchanged, and its affine eigenvalues are precisely the
transformed nodes, so the characteristic polynomial is their monic product. -/
theorem shiftedFibre_inFiber {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {z:ℝ} (hz:0<z) (ht:∀k,S.value k<z) :
    InFiber (shiftedFibre J z) (shiftedNodes S z hz ht).polynomial := by
  -- Spectral labels are retained for every competitor, not chosen only for the target chain.
  refine ⟨affine_irreducible hJ.1 (inv_ne_zero (shiftScale_pos hz).ne') _,?_⟩
  let B := orderedBasis S J hJ
  let B' := affineBasis J B (inv_nonneg.mpr (shiftScale_pos hz).le) (shiftTranslation z/shiftScale z)
  change (affine J (shiftScale z)⁻¹ (shiftTranslation z/shiftScale z)).matrix.charpoly=_
  rw [B'.charpoly_factor]
  apply Finset.prod_congr rfl
  intro k _
  congr 2
  change (shiftScale z)⁻¹*B.eigenvalues k+shiftTranslation z/shiftScale z=_
  rw [show B.eigenvalues k=S.value k from congrFun (orderedBasis_values S J hJ) k]
  dsimp only [shiftedNodes]
  ring

/-- The transformed Green matrix is exactly theta times the genuine original shifted inverse.
Use: shiftedFibre_energy transfers the original shifted squared-diagonal objective.
Article: jacobi, Theorem C.5.
Source: scalar multiplication of an invertible finite matrix.
Proof: the actual affine matrix identity gives I-J'=theta^(-1)(zI-J).
The source point is outside the actual spectrum by its strict node gaps,
so the community matrix inverse scaling identity applies. -/
theorem shiftedFibre_green {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {z:ℝ} (hz:0<z) (ht:∀k,S.value k<z) :
    (shiftedFibre J z).green=shiftScale z • (z • (1:Matrix (Fin N) (Fin N) ℝ)-J.matrix)⁻¹ := by
  -- The determinant premise is proved for the same matrix as the inverse in the objective.
  have hspec : z∉spectrum ℝ J.matrix := by
    rw [S.spectrum_eq hJ]
    rintro ⟨k,hk⟩
    exact (ht k).ne hk
  have hu : IsUnit (z • (1:Matrix (Fin N) (Fin N) ℝ)-J.matrix) := by
    simpa only [spectrum.mem_iff,not_not,Algebra.algebraMap_eq_smul_one] using hspec
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have htheta := (shiftScale_pos hz).ne'
  let _ : Invertible ((shiftScale z)⁻¹) := invertibleOfNonzero (inv_ne_zero htheta)
  have he : (1:Matrix (Fin N) (Fin N) ℝ)-(shiftedFibre J z).matrix=
      (shiftScale z)⁻¹ • (z • (1:Matrix (Fin N) (Fin N) ℝ)-J.matrix) := by
    rw [shiftedFibre,affine_matrix J (inv_nonneg.mpr (shiftScale_pos hz).le)]
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply]
    have ht : shiftScale z=z+shiftTranslation z := rfl
    split_ifs <;> field_simp [htheta] <;> nlinarith [ht]
  rw [Jacobi.green,he,Matrix.inv_smul _ _ hd,invOf_eq_inv,inv_inv]

/-- The original transformed energy has exactly the source's theta-squared factor.
Use: the real-shift lower bound removes theta_N -> 1 after applying full Transfer.
Article: jacobi, Theorem C.5.
Proof: square the proved exact original Green matrix identity and factor
the same scalar out of the finite sum of actual diagonal squares. -/
theorem shiftedFibre_energy {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {z:ℝ} (hz:0<z) (ht:∀k,S.value k<z) :
    (shiftedFibre J z).energy=shiftScale z^2*
      ∑i:Fin N,((z • (1:Matrix (Fin N) (Fin N) ℝ)-J.matrix)⁻¹ i i)^2 := by
  simp only [Jacobi.energy,shiftedFibre_green S hJ hz ht,Matrix.smul_apply,smul_eq_mul,mul_pow]
  exact (Finset.mul_sum ..).symm

end
end jacobi.Finite
