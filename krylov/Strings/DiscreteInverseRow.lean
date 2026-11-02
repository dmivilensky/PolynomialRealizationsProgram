import krylov.Strings.DiscreteInverseSetup
import krylov.Strings.DiscreteDivergence

/-!
Article: `main_krylov`, `apC:lem:stieltjes(b)`.
Exact genuine Jacobi row action and the actual zero-energy harmonic
vector give the sign of the inverse Robin boundary coefficient. This
uses positive semidefiniteness of the reconstructed physical matrix,
rather than assuming the proposed boundary condition is admissible.
-/

namespace krylov.Strings.DiscreteInverse
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator

/-- Literal action of a genuine finite Jacobi matrix on a natural-number
indexed vector, with both physical boundary terms explicit. -/
theorem jacobi_row_action {n : ℕ} (J : Jacobi n) (v : ℕ→ℝ) (i : Fin n) :
    (J.matrix *ᵥ (fun j ↦ v j.val)) i=
      J.data.b i.val*v i.val+
      (if i.val+1<n then Real.sqrt (J.data.aSq (i.val+1))*v (i.val+1) else 0)+
      (if 0 < i.val then Real.sqrt (J.data.aSq i.val)*v (i.val-1) else 0) := by
  have he (j : Fin n) : J.matrix i j*v j.val=
      (if j.val=i.val then J.data.b i.val*v j.val else 0)+
      (if j.val=i.val+1 then Real.sqrt (J.data.aSq (i.val+1))*v j.val else 0)+
      (if j.val=i.val-1 then (if 0 < i.val then Real.sqrt (J.data.aSq i.val)*v j.val else 0) else 0) := by
    simp only [Jacobi.matrix, JacobiData.matrix_apply, Nat.zero_add]
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      have hne : i.val≠i.val+1 := by omega
      rw [ite_eq_right hne]
      by_cases hi : 0 < i.val
      · rw [ite_eq_left hi, ite_eq_right (by omega : i.val≠i.val-1)]
        ring
      · rw [ite_eq_right hi]
        split_ifs <;> ring
    · have hne : j.val≠i.val := by intro he; exact hij (Fin.ext he.symm)
      simp only [ite_eq_right hij, ite_eq_right hne, zero_add]
      by_cases hu : i.val+1=j.val
      · have hl : ¬j.val+1=i.val := by omega
        rw [ite_eq_left hu, ite_eq_left hu.symm, ← hu,
          ite_eq_right (by omega : i.val+1≠i.val-1)]
        simp
      · by_cases hl : j.val+1=i.val
        · have hi : 0 < i.val := by omega
          rw [ite_eq_right hu, ite_eq_left hl, ite_eq_right (by omega : j.val≠i.val+1),
            ite_eq_left (by omega : j.val=i.val-1), ite_eq_left hi]
          simp
        · rw [ite_eq_right hu, ite_eq_right hl, ite_eq_right (by omega : j.val≠i.val+1)]
          by_cases hi : 0 < i.val
          · rw [ite_eq_right (by omega : j.val≠i.val-1)]
            simp
          · rw [ite_eq_right hi]
            simp
  change (∑ j, J.matrix i j*v j.val)=_
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    DiscreteString.sum_edge_site, DiscreteString.sum_edge_site, DiscreteString.sum_edge_site]
  rw [dite_eq_left i.isLt]
  by_cases hi : 0 < i.val
  · rw [dite_eq_left (by omega : i.val-1<n), ite_eq_left hi]
    split_ifs <;> rfl
  · simp only [ite_eq_right hi]
    split_ifs <;> simp

variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- The actual zero-energy canonical polynomial vector. -/
def zeroVector : Fin (N+1)→ℝ := fun i ↦ (-1 : ℝ)^i.val*zeroValue M i.val

/-- True inverse Robin boundary coefficient, derived from the final
physical row of the independently reconstructed Jacobi matrix. -/
def robin : ℝ := M.reconstructed.data.b N*zeroValue M N^2-
  (if 0<N then coupling M (N-1)*zeroValue M (N-1)*zeroValue M N else 0)

/-- The actual reconstructed Jacobi energy of its canonical zero-energy
vector is exactly the proposed physical terminal Robin coefficient. -/
theorem zeroVector_energy :
    zeroVector M ⬝ᵥ (M.reconstructed.matrix *ᵥ zeroVector M)=robin M := by
  have hrow (i : Fin (N+1)) :
      (M.reconstructed.matrix *ᵥ zeroVector M) i=
        M.reconstructed.data.b i.val*zeroVector M i+
        (if i.val+1<N+1 then coupling M i.val*((-1 : ℝ)^(i.val+1)*zeroValue M (i.val+1)) else 0)+
        (if 0 < i.val then coupling M (i.val-1)*((-1 : ℝ)^(i.val-1)*zeroValue M (i.val-1)) else 0) := by
    have h := jacobi_row_action M.reconstructed (fun j ↦ (-1 : ℝ)^j*zeroValue M j) i
    dsimp only [zeroVector]
    change (M.reconstructed.matrix *ᵥ (fun j : Fin (N+1) ↦ (-1 : ℝ)^j.val*zeroValue M j.val)) i=_
    rw [h]
    by_cases hi : 0 < i.val
    · simp only [coupling, ite_eq_left hi]
      rw [show i.val-1+1=i.val by omega]
    · simp only [coupling, ite_eq_right hi]
  let last : Fin (N+1) := ⟨N,by omega⟩
  change (∑ i, zeroVector M i*(M.reconstructed.matrix *ᵥ zeroVector M) i)=_
  rw [Finset.sum_eq_single last]
  · rw [hrow]
    have hs := alternating_sq N
    simp only [last, lt_self_iff_false, zeroVector]
    rw [ite_false, add_zero]
    by_cases hN : 0<N
    · rw [ite_eq_left hN, robin, ite_eq_left hN]
      have he : N-1+1=N := by omega
      have hs' : (-1 : ℝ)^(N-1)=-(-1 : ℝ)^N := by
        have ht : (-1 : ℝ)^N=(-1 : ℝ)^(N-1)*(-1) := by
          conv_lhs => rw [← he]
          exact pow_succ _ _
        linear_combination ht
      rw [hs']
      linear_combination (M.reconstructed.data.b N*zeroValue M N^2-
        coupling M (N-1)*zeroValue M (N-1)*zeroValue M N)*hs
    · rw [ite_eq_right hN, robin, ite_eq_right hN]
      linear_combination M.reconstructed.data.b N*zeroValue M N^2*hs
  · intro i _ hi
    have hil : i.val<N := by
      have hne : i.val≠N := by intro he; apply hi; exact Fin.ext he
      omega
    rw [hrow, ite_eq_left (by omega : i.val+1<N+1)]
    have hb := zeroValue_balance M i.val hil
    by_cases hi0 : 0 < i.val
    · rw [ite_eq_left hi0]
      have hk0 : i.val≠0 := by omega
      rw [ite_eq_right hk0] at hb
      have he : i.val-1+1=i.val := by omega
      have hs' : (-1 : ℝ)^(i.val-1)=-(-1 : ℝ)^i.val := by
        have ht : (-1 : ℝ)^i.val=(-1 : ℝ)^(i.val-1)*(-1) := by
          conv_lhs => rw [← he]
          exact pow_succ _ _
        linear_combination ht
      simp only [zeroVector, pow_succ]
      rw [hs']
      linear_combination ((-1 : ℝ)^i.val)^2*zeroValue M i.val*hb
    · have hi0' : i.val=0 := by omega
      rw [ite_eq_right hi0, ite_eq_left hi0'] at *
      simp only [hi0', zero_add, add_zero] at hb
      simp only [zeroVector, hi0', zero_add, pow_zero, pow_one, one_mul, add_zero]
      linear_combination zeroValue M 0*hb
  · simp

/-- The inverse Robin boundary is nonnegative for every prescribed
nonnegative finite spectral probability, with no boundary sign assumption. -/
theorem robin_nonneg (hnode : ∀ i,0≤M.node i) : 0≤robin M := by
  have h := (reconstructed_posSemidef M hnode).dotProduct_mulVec_nonneg (zeroVector M)
  simp only [star_trivial] at h
  rwa [zeroVector_energy] at h

end
end krylov.Strings.DiscreteInverse
