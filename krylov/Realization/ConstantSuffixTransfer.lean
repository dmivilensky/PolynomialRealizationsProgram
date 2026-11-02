import krylov.Realization.AffineUnrolling
import krylov.Realization.InsertionPolynomials
import chebyshev1.TwoTerm.Operator

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine constant-memory suffix variation of constants.
Use: identify the true suffix transfer of any actual constant-preserving finite-memory realization with its genuine independent injection tails.
Source: the existing actual affine unrolling, real chronological ordered products and the genuine matrix/linear-map algebra equivalence.
-/

namespace krylov.Realization
noncomputable section
open chebyshev1 Matrix
open scoped BigOperators
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- A genuine affine recurrence preserving the true constant state has its actual homogeneous transfer equal to that state minus all real independent tail responses.
Use: A genuine affine recurrence preserving the true constant state has its actual homogeneous transfer equal to that state minus all real independent tail responses.
Article: main_krylov, prop:phi(a), genuine constant-memory suffix variation of constants.
Proof: The actual affine execution is constant; substitute it into the proved genuine finite variation-of-constants formula. -/
theorem transfer_constant_affine (C : ℕ → F →ₗ[ℝ] F) (input : ℕ → F) (b : F) (N : ℕ)
    (h : ∀ k<N,C k b+input k=b) :
    orderedProduct C N b=b-∑ s∈Finset.range N,
      orderedProduct (fun i => C (s+1+i)) (N-(s+1)) (input s) := by
  have hc : affineRun C input b N=b := by
    induction N with
    | zero => rfl
    | succ N ih => rw [affineRun,ih (fun i hi => h i (by omega)),h N (by omega)]
  rw [affineRun_unroll] at hc
  exact eq_sub_of_add_eq hc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every actual finite-memory scalar suffix preserving the genuine constant state has its true transfer equal to that state minus the real summed oracle-input tails.
Use: Every actual finite-memory scalar suffix preserving the genuine constant state has its true transfer equal to that state minus the real summed oracle-input tails.
Article: main_krylov, prop:phi(a), genuine constant-memory suffix variation of constants.
Proof: Apply actual affine unrolling to the true scalar matrix recurrence and transfer its genuine chronological tails through the matrix/linear-map equivalence. -/
theorem scalar_suffix_constant (R : chebyshev1.Realization ι)
    (j k : ℕ) (b : ι → ℝ) (lam : ℝ)
    (hP : ∀ i<k,R.P (j+i) *ᵥ b=b) (hq : ∀ i<k,R.q (j+i) ⬝ᵥ b=1) :
    orderedProduct (fun i => R.scalarStep (j+i) lam) k *ᵥ b=
      b-lam • ∑ s∈Finset.range k,
        orderedProduct (fun i => R.scalarStep (j+s+1+i) lam) (k-(s+1)) *ᵥ R.g (j+s) := by
  -- The actual scalar pencil plus its genuine query injection preserves the real constant memory state.
  let C := fun i => Matrix.toLinAlgEquiv' (R.scalarStep (j+i) lam)
  have hc (i : ℕ) (hi : i<k) : C i b+lam • R.g (j+i)=b := by
    dsimp only [C]
    rw [Matrix.toLinAlgEquiv'_apply,Realization.scalarStep,Matrix.sub_mulVec,
      Realization.queryFactor,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,hq i hi]
    simp only [op_smul_eq_smul,one_smul]
    rw [sub_add_cancel,hP i hi]
  have he := transfer_constant_affine C (fun i => lam • R.g (j+i)) b k hc
  -- Transfer the genuine chronological operator products through the actual matrix algebra equivalence, without reversing any true tail.
  have hm (a p : ℕ) : orderedProduct (fun i => C (a+i)) p=
      Matrix.toLinAlgEquiv' (orderedProduct (fun i => R.scalarStep (j+a+i) lam) p) := by
    simpa [C,Nat.add_assoc] using
      (orderedProduct_map (Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ] _).toMonoidHom
        (fun i => R.scalarStep (j+a+i) lam) p).symm
  have htop : orderedProduct C k=
      Matrix.toLinAlgEquiv' (orderedProduct (fun i => R.scalarStep (j+i) lam) k) := by
    simpa only [Nat.zero_add,Nat.add_zero] using hm 0 k
  -- Each actual finite injection tail keeps its real starting index and genuine scalar factor.
  rw [htop] at he
  simp only [Matrix.toLinAlgEquiv'_apply] at he
  rw [he]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [hm]
  simp only [Matrix.toLinAlgEquiv'_apply,Matrix.mulVec_smul,Nat.add_assoc]
end
end krylov.Realization
