import jacobi.Comparison.GramHalfRows
import jacobi.Comparison.GramReflection
import jacobi.Finite.HalfRows

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The actual finite Gram perturbation splits exactly into its original
right half and the reflected strict half for the exchanged parameters.
Both complete growing spectral rows have their genuine GL limits;
their combination retains the actual alternating matrix-index sign.
Use: gramPerturbation_two_edge_limit combines the independently proved full growing spectral half-row limits without omitting or double-counting an original middle node.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter Finset jacobi.Support jacobi.Reference
open scoped Topology

/-- The entire actual original Gram perturbation is exactly its right spectral half plus the alternating strict reflected half for the exchanged parameters.
Use: gramPerturbation_two_edge_limit combines the independently proved full growing spectral half-row limits without omitting or double-counting an original middle node.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the genuine target Gram perturbation equals its original full spectral summand row. Apply the exact finite two-half partition; reflection of each actual opposite-edge summand gives the original canonical alternating factor, which is constant over that spectral half-row. -/
theorem gramPerturbation_two_halves (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) :
    ((n:ℝ)+1)*gramPerturbation a b ha hb n i j=
      (∑k∈range (n+1),gramHalfTerm false a b ha hb n i j k)+
      (-1:ℝ)^(i.val+j.val)*(∑k∈range (n+1),gramHalfTerm true b a hb ha n i j k) := by
  -- The possible original middle spectral node belongs only to the first half.
  have hsum : gramPerturbation a b ha hb n i j=∑k∈range (n+1),gramSummandAt a b ha hb n i j k := by
    rw [gramPerturbation_sum]
    calc
      _ = ∑k:Fin (n+1),gramSummandAt a b ha hb n i j k.val := by
        apply sum_congr rfl
        intro k _
        simp only [gramSummandAt,dite_eq_left k.isLt]
      _ = _ := Fin.sum_univ_eq_sum_range _ _
  rw [hsum,jacobi.Finite.sum_two_halves,mul_add,mul_sum,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro k _
    by_cases hk:2*k≤n <;> simp only [gramHalfTerm,Bool.false_eq_true,ite_false,hk,
      ite_true,mul_zero]
  · rw [mul_sum]
    apply sum_congr rfl
    intro k hkN
    have hk : k≤n := by have := Finset.mem_range.mp hkN; omega
    by_cases hhalf:2*k<n
    · change ((n:ℝ)+1)*(if 2*k<n then gramSummandAt a b ha hb n i j (n-k) else 0)=
        (-1:ℝ)^(i.val+j.val)*(if 2*k<n then ((n:ℝ)+1)*gramSummandAt b a hb ha n i j k else 0)
      rw [ite_eq_left hhalf,ite_eq_left hhalf,gramSummandAt_reflection ha hb n i j hk]
      ring
    · change ((n:ℝ)+1)*(if 2*k<n then gramSummandAt a b ha hb n i j (n-k) else 0)=
        (-1:ℝ)^(i.val+j.val)*(if 2*k<n then ((n:ℝ)+1)*gramSummandAt b a hb ha n i j k else 0)
      simp only [ite_eq_right hhalf,mul_zero]

/-- The actual full matrix-size-scaled Gram perturbation has both complete original spectral-edge limits along arbitrary moving physical half-chain row and column indices, retaining its true alternating sign.
Use: the uniform two-edge matrix and coercivity arguments use the actual full spectral decomposition; this theorem completes its finite-to-infinite summation at both original edges without a missing tail assumption.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the complete genuine right spectral row converges to F_alpha and the complete strict reflected row converges to F_beta. Subtract those two limits in the exact original half-row identity. The genuine alternating sign has absolute value one at every original dimension, so the norm of the total error is bounded by the sum of the two independently vanishing original row errors. -/
theorem gramPerturbation_two_edge_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i j:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    (hj:∀ᶠn:ℕ in atTop,2*(j n).val≤ns n+1) {t s:ℝ}
    (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun n:ℕ => ((j n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n:ℕ => ((ns n:ℝ)+1)*gramPerturbation a b ha hb (ns n) (i n) (j n)-
      (jacobi.GelfandLevitan.kernel a ha t s+
        (-1:ℝ)^((i n).val+(j n).val)* jacobi.GelfandLevitan.kernel b hb t s)) atTop (𝓝 0) := by
  -- No parity subsequence is required: the actual alternating factor has unit absolute value throughout.
  let R (n:ℕ) := ∑k∈range (ns n+1),gramHalfTerm false a b ha hb (ns n) (i n) (j n) k
  let S (n:ℕ) := ∑k∈range (ns n+1),gramHalfTerm true b a hb ha (ns n) (i n) (j n) k
  have hR := (gramHalfRow_limit false ha hb ns hns i j hi hj ht hs hit hjs).sub_const
    (jacobi.GelfandLevitan.kernel a ha t s)
  have hS := (gramHalfRow_limit true hb ha ns hns i j hi hj ht hs hit hjs).sub_const
    (jacobi.GelfandLevitan.kernel b hb t s)
  simp only [sub_self] at hR hS
  apply squeeze_zero_norm _ (by simpa only [norm_zero,zero_add] using hR.norm.add hS.norm)
  intro n
  rw [gramPerturbation_two_halves]
  have he : R n+(-1:ℝ)^((i n).val+(j n).val)*S n-
      (jacobi.GelfandLevitan.kernel a ha t s+
        (-1:ℝ)^((i n).val+(j n).val)* jacobi.GelfandLevitan.kernel b hb t s)=
      (R n- jacobi.GelfandLevitan.kernel a ha t s)+(-1:ℝ)^((i n).val+(j n).val)*
        (S n- jacobi.GelfandLevitan.kernel b hb t s) := by ring
  change ‖R n+_ * S n-(_+_ * _)‖≤_
  rw [he]
  simpa only [norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,abs_one,one_pow,one_mul] using
    norm_add_le (R n- jacobi.GelfandLevitan.kernel a ha t s)
      ((-1:ℝ)^((i n).val+(j n).val)*(S n- jacobi.GelfandLevitan.kernel b hb t s))

end
end jacobi.Comparison
