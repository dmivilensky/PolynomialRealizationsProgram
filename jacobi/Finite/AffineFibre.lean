import jacobi.Finite.AffinePolynomials
import jacobi.Finite.AffineSpectrum
import jacobi.Variational.Transfer
import chebyshev2.Finite.MatrixExt

/-!
Article: jacobi, Proposition 6.1.
A positive affine map fixing one preserves every positive coupling
and scales the genuine Green energy by theta^(-2). Its inverse acts
on all competitors, so the full original fibre infimum has exactly
the same scale factor. This finite statement retains information
which the limiting edge spectrum alone cannot recover.
Use: endpointAffine_inFiber and endpointAffine_energy transform the entire source fibre in the counterexample.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Polynomial Set Filter chebyshev1 chebyshev2 jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual positive affine transformation fixing the resolvent point one.
Use: endpointAffine_inFiber and endpointAffine_energy transform the entire source fibre in the counterexample.
Article: jacobi, Proposition 6.1.
-/
def endpointAffine {N:ℕ} (J:Jacobi N) (theta:ℝ) : Jacobi N :=
  affine J theta (1-theta)

/-- The actual endpoint-fixing affine transformation maps every original fibre competitor to the full affine-image polynomial fibre.
Use: endpointAffineEquiv includes all realizations when comparing source infima.
Article: jacobi, Proposition 6.1.
Proof: keep the actual original ordered spectral basis. Positive
affine scaling changes every genuine eigenvalue to its prescribed
target node and preserves all actual positive internal couplings. -/
theorem endpointAffine_inFiber {N:ℕ} (S T:Nodes N) {theta:ℝ} (ht:0 < theta)
    (hnode:∀i,T.value i=theta*S.value i+(1-theta)) {J:Jacobi N}
    (hJ:InFiber J S.polynomial) : InFiber (endpointAffine J theta) T.polynomial := by
  -- The spectral argument is for an arbitrary original competitor.
  refine ⟨affine_irreducible hJ.1 ht.ne' _,?_⟩
  let B:=orderedBasis S J hJ
  let C:=affineBasis J B ht.le (1-theta)
  change (affine J theta (1-theta)).matrix.charpoly=_
  rw [C.charpoly_factor]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  change theta*B.eigenvalues i+(1-theta)=T.value i
  rw [show B.eigenvalues i=S.value i from congrFun (orderedBasis_values S J hJ) i,hnode]

/-- The actual endpoint-fixing affine map has its genuine inverse on the full original finite Jacobi type.
Use: endpointAffineEquiv is a true bijection of complete original fibres, including canonical coefficient tails.
Article: jacobi, Proposition 6.1.
Proof: apply the existing injectivity of finite Jacobi matrix encoding.
The two exact affine matrix identities cancel their positive scales
and translations entry by entry. -/
theorem endpointAffine_inverse {N:ℕ} (J:Jacobi N) {theta:ℝ} (ht:0 < theta) :
    endpointAffine (endpointAffine J theta) theta⁻¹=J := by
  -- Matrix injectivity also recovers the original fixed zero tails.
  apply Jacobi.matrix_injective
  rw [endpointAffine,affine_matrix _ (inv_nonneg.mpr ht.le),endpointAffine,affine_matrix _ ht.le]
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.scalar_apply,Matrix.diagonal_apply,smul_eq_mul]
  split_ifs <;> field_simp [ht.ne'] <;> ring

/-- The complete original fibre and its prescribed positive affine image are equivalent through the genuine matrix transformation.
Use: fibreEnergyInfimum_endpointAffine changes variables in the full infimum, without restricting to a chosen matrix family.
Article: jacobi, Proposition 6.1.
-/
def endpointAffineEquiv {N:ℕ} (S T:Nodes N) {theta:ℝ} (ht:0 < theta)
    (hnode:∀i,T.value i=theta*S.value i+(1-theta)) :
    Fiber N S.polynomial ≃ Fiber N T.polynomial where
  toFun J:=⟨endpointAffine J.val theta,endpointAffine_inFiber S T ht hnode J.property⟩
  invFun J:=⟨endpointAffine J.val theta⁻¹,endpointAffine_inFiber T S (inv_pos.mpr ht)
    (fun i=>by rw [hnode]; field_simp [ht.ne']; ring) J.property⟩
  left_inv J:=Subtype.ext (endpointAffine_inverse J.val ht)
  right_inv J:=Subtype.ext (by
    simpa only [inv_inv] using endpointAffine_inverse J.val (inv_pos.mpr ht))

/-- The genuine Green matrix of every original fibre competitor has exactly the inverse affine scale.
Use: endpointAffine_energy transfers the actual squared-diagonal objective.
Article: jacobi, Proposition 6.1.
Proof: the exact actual pencil is theta*(I-J). Its determinant is
nonzero because the full original prescribed spectrum lies below one.
The community inverse-scaling identity applies to this unchanged pencil. -/
theorem endpointAffine_green {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {theta:ℝ} (ht:0 < theta) : (endpointAffine J theta).green=theta⁻¹ • J.green := by
  -- Invertibility is proved for the actual source matrix before scaling its inverse.
  have hu:=J.affine_posDef 1 (-1) (fun x hx=>by
    rw [S.spectrum_eq hJ] at hx
    obtain ⟨i,rfl⟩:=hx
    linarith [(S.interval i).2])
  have hp:(1-J.matrix).PosDef:=by simpa [Matrix.scalar,sub_eq_add_neg] using hu
  have hd: IsUnit ((1-J.matrix).det):=(Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
  let _ : Invertible theta:=invertibleOfNonzero ht.ne'
  have he:(1:Matrix (Fin N) (Fin N) ℝ)-(endpointAffine J theta).matrix=theta • (1-J.matrix) := by
    rw [endpointAffine,affine_matrix J ht.le]
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
      Matrix.scalar_apply,Matrix.diagonal_apply,smul_eq_mul]
    split_ifs <;> ring
  rw [Jacobi.green,he,Matrix.inv_smul _ _ hd,invOf_eq_inv]
  rfl

/-- The true Green energy of every original affine fibre competitor scales exactly by theta^(-2).
Use: fibreEnergyInfimum_endpointAffine transfers the complete original infimum, not just a candidate upper bound.
Article: jacobi, Proposition 6.1.
Proof: square each actual diagonal in the proved genuine Green identity and factor the same scalar out of the full finite sum. -/
theorem endpointAffine_energy {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {theta:ℝ} (ht:0 < theta) : (endpointAffine J theta).energy=theta⁻¹^2*J.energy := by
  simp only [Jacobi.energy,endpointAffine_green S hJ ht,Matrix.smul_apply,smul_eq_mul,mul_pow]
  exact (Finset.mul_sum ..).symm

/-- The actual normalized full-fibre infimum has the exact positive endpoint-affine scale theta^(-2).
Use: the U branch of Proposition 6.1 inherits its whole optimal-energy limit from the genuine U fibre.
Article: jacobi, Proposition 6.1.
Proof: express each original infimum over its genuine fibre subtype.
The proved actual affine equivalence changes variables in that whole
domain, and its exact actual energy scale factors through the infimum
by the community positive finite ENNReal infimum identity. -/
theorem fibreEnergyInfimum_endpointAffine {N:ℕ} (S T:Nodes N) {theta:ℝ} (ht:0 < theta)
    (hnode:∀i,T.value i=theta*S.value i+(1-theta)) :
    fibreEnergyInfimum T=ENNReal.ofReal (theta⁻¹^2)*fibreEnergyInfimum S := by
  -- The equality preserves every original competitor and the same matrix-dimension normalization.
  have hr (R:Nodes N) : fibreEnergyInfimum R=⨅J:Fiber N R.polynomial,fibreCost J.val := by
    simp only [fibreEnergyInfimum,sInf_image,iInf_subtype,Set.mem_ofPred_eq]
  rw [hr T,hr S,ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top]
  let e:=endpointAffineEquiv S T ht hnode
  rw [← Equiv.iInf_comp e]
  apply iInf_congr
  intro J
  change fibreCost (endpointAffine J.val theta)=ENNReal.ofReal (theta⁻¹^2)*fibreCost J.val
  rw [fibreCost,endpointAffine_energy S J.property ht,mul_div_assoc,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rfl

end
end jacobi.Finite
