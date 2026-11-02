import krylov.LinearAlgebra.PlanarWitness
import krylov.LinearAlgebra.RankOneNorm
import krylov.Convergence.SS1FModel

/-!
Article: main_krylov, thm:ss1F, the sharp leading corrected matrix.
Use: retain the exact oldest diagonal plus adjacent symmetric cross-entry
without a Frobenius factor or a dimension factor in the leading constant.
Source: the previously proved two-plane spectral action and finite Bessel
inequality; only the remaining entries use the coarse Frobenius bound.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine two-entry symmetric leading model on an orthonormal plane. -/
def leadingValueMatrix (e h : EuclideanSpace ℝ (Fin n)) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  a • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)+
    b • (vecMulVec (WithLp.ofLp e) (WithLp.ofLp h)+vecMulVec (WithLp.ofLp h) (WithLp.ofLp e))

/-- The exact leading symmetric matrix costs at most |oldest diagonal| +
|adjacent cross-entry|, with no factor two on the cross-entry. -/
theorem leadingValueMatrix_norm (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (a b : ℝ) :
    ‖leadingValueMatrix e h a b‖≤|a|+|b| := by
  have houter : ‖vecMulVec (WithLp.ofLp e) (WithLp.ofLp e)‖=1 := by
    have ho := spectral_norm_rankOne (WithLp.ofLp e) (WithLp.ofLp e)
    simpa only [chebyshev1.opNorm,WithLp.toLp_ofLp,he,mul_one] using ho
  have hcross : ‖vecMulVec (WithLp.ofLp e) (WithLp.ofLp h)+
      vecMulVec (WithLp.ofLp h) (WithLp.ofLp e)‖≤1 := by
    have hc := planar_spectral_norm_le e h he hh heh 0 1 (by norm_num)
    simpa only [chebyshev1.opNorm,planarMatrix,neg_zero,zero_smul,one_smul,zero_add,add_zero] using hc
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,houter,mul_one]
  exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcross (abs_nonneg b))

/-- The concrete first-two-coordinate leading model. -/
def oldestLeadingMatrix (a b : ℝ) : Matrix (Fin (n+2)) (Fin (n+2)) ℝ :=
  leadingValueMatrix (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) a b

/-- Exact standard-coordinate form of the leading matrix. -/
theorem oldestLeadingMatrix_apply (a b : ℝ) (i j : Fin (n+2)) :
    oldestLeadingMatrix (n:=n) a b i j=
      if i=0 ∧j=0 then a else if (i=0 ∧j=1) ∨(i=1 ∧j=0) then b else 0 := by
  simp only [oldestLeadingMatrix,leadingValueMatrix,Matrix.add_apply,Matrix.smul_apply,
    vecMulVec_apply,PiLp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

/-- The actual coordinate leading matrix preserves the sharp coefficient. -/
theorem oldestLeadingMatrix_norm (a b : ℝ) :
    ‖oldestLeadingMatrix (n:=n) a b‖≤|a|+|b| := by
  apply leadingValueMatrix_norm
  · simp only [PiLp.norm_single,norm_one]
  · simp only [PiLp.norm_single,norm_one]
  · rw [EuclideanSpace.inner_single_left]
    norm_num [PiLp.single_apply]

/-- Subtracting the exact oldest diagonal and adjacent symmetric entry
leaves only the other actual entries. Their spectral cost is a remainder. -/
theorem oldest_leading_remainder_bound (X : Matrix (Fin (n+2)) (Fin (n+2)) ℝ)
    (hX : X.IsSymm) {ε : ℝ} (hε : 0≤ε)
    (hother : ∀ i j,¬(i=0 ∧j=0) → ¬((i=0 ∧j=1) ∨(i=1 ∧j=0)) → |X i j|≤ε) :
    ‖X‖≤|X 0 0|+|X 0 1|+((n+2:ℕ):ℝ)*ε := by
  let L := oldestLeadingMatrix (n:=n) (X 0 0) (X 0 1)
  have hr : ‖X-L‖≤((n+2:ℕ):ℝ)*ε := by
    apply (spectral_le_hsNorm _).trans
    apply hsNorm_le_dimension _ hε
    intro i j
    change |X i j-oldestLeadingMatrix (X 0 0) (X 0 1) i j|≤ε
    rw [oldestLeadingMatrix_apply]
    split_ifs with hij hcross
    · rcases hij with ⟨rfl,rfl⟩
      simpa only [sub_self,abs_zero] using hε
    · rcases hcross with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simpa only [sub_self,abs_zero] using hε
      · have hs : X 1 0=X 0 1 := hX.apply 0 1
        simpa only [hs,sub_self,abs_zero] using hε
    · simpa only [sub_zero] using hother i j hij hcross
  have he : X=L+(X-L) := by abel
  calc
    ‖X‖ = ‖L+(X-L)‖ := congrArg norm he
    _ ≤ ‖L‖+‖X-L‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (oldestLeadingMatrix_norm _ _) hr

end
end krylov.Convergence
