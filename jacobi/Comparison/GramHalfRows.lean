import jacobi.Comparison.GramEdgeTerms
import jacobi.Analysis.SmallRemainderSum
import jacobi.GelfandLevitan.UniformKernel

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The complete growing original right spectral half-row tends to the
actual continuum GL kernel along arbitrary moving physical matrix
indices. Both middle-index conventions are covered, with the actual
little-o remainder summed over the true finite dimension.
Use: gramHalfRow_limit proves both the complete right-edge kernel limit and the strict half-row needed after reflection for the opposite spectral edge.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter Finset jacobi.Support jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- One actual spectral half of the original matrix-size-scaled Gram row, with its original middle-point convention.
Use: gramHalfRow_limit proves both the complete right-edge kernel limit and the strict half-row needed after reflection for the opposite spectral edge.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def gramHalfTerm (strict:Bool) (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) (k:ℕ) : ℝ :=
  if (if strict then 2*k<n else 2*k≤n) then
    ((n:ℝ)+1)*gramSummandAt a b ha hb n i j k else 0

/-- Each genuine fixed spectral term eventually belongs to either original half-row convention and has the actual GL kernel summand limit.
Use: gramHalfRow_limit sums all original growing spectral indices using the proved uniform inverse-square bound and vanishing total remainder.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the fixed index eventually lies strictly below the actual spectral midpoint, so either exact cutoff retains its unchanged original Gram summand. Apply the already proved genuine fixed-summand limit. -/
theorem gramHalfTerm_limit (strict:Bool) {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i j:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    (hj:∀ᶠn:ℕ in atTop,2*(j n).val≤ns n+1) {t s:ℝ}
    (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun n:ℕ => ((j n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n:ℕ => gramHalfTerm strict a b ha hb (ns n) (i n) (j n) k) atTop
      (𝓝 (jacobi.GelfandLevitan.kernelTerm a ha k t s)) := by
  -- A fixed original spectral index eventually belongs to either half-row convention.
  apply (gramSummandAt_limit ha hb k ns hns i j hi hj ht hs hit hjs).congr'
  filter_upwards [hns.eventually_gt_atTop (2*k)] with n hn
  cases strict with
  | false =>
    change _=(if 2*k≤ns n then ((ns n:ℝ)+1)*gramSummandAt a b ha hb (ns n) (i n) (j n) k else 0)
    rw [ite_eq_left hn.le]
  | true =>
    change _=(if 2*k<ns n then ((ns n:ℝ)+1)*gramSummandAt a b ha hb (ns n) (i n) (j n) k else 0)
    rw [ite_eq_left hn]

/-- The entire original growing spectral half-row converges to the actual source GL kernel for either exact middle-index convention.
Use: exact reflection of the original left spectral half combines this limit for the exchanged parameters with its right counterpart to give the full alternating two-edge Gram limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: every actual half-row term has the proved uniform bound C/(k+1)^2+epsilon_n because its true edge index is k+1. The p-series part is summable, the total original remainder tends to zero, and every fixed term has its genuine original kernelTerm limit. The finite-row convergence theorem sums the complete growing half-row, including its actual tail. -/
theorem gramHalfRow_limit (strict:Bool) {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop)
    (i j:∀n:ℕ,Fin (ns n+1)) (hi:∀ᶠn:ℕ in atTop,2*(i n).val≤ns n+1)
    (hj:∀ᶠn:ℕ in atTop,2*(j n).val≤ns n+1) {t s:ℝ}
    (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun n:ℕ => ((i n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun n:ℕ => ((j n).val:ℝ)/(ns n:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n:ℕ => ∑k∈range (ns n+1),gramHalfTerm strict a b ha hb (ns n) (i n) (j n) k) atTop
      (𝓝 (jacobi.GelfandLevitan.kernel a ha t s)) := by
  -- The genuine original spectral remainder is retained until its whole finite row has been summed.
  obtain ⟨C,hC,ε,hε,hεlim,hbound⟩ := gramSummand_bound ha hb
  apply jacobi.Analysis.finite_row_small_remainder
    (f:=fun n k => gramHalfTerm strict a b ha hb (ns n) (i n) (j n) k)
    (F:=fun k => jacobi.GelfandLevitan.kernelTerm a ha k t s)
    (N:=ns) (g:=fun k => C/(k+1:ℝ)^2) (ε:=fun n => ε (ns n))
    (fun k => by positivity)
    (by simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C)
    (fun n => hε (ns n)) (hεlim.comp hns)
  · intro n k hnk
    have hcut : ¬(if strict then 2*k<ns n else 2*k≤ns n) := by
      cases strict with
      | false => change ¬2*k≤ns n; omega
      | true => change ¬2*k<ns n; omega
    exact ite_eq_right hcut
  · filter_upwards [hns.eventually hbound,hi,hj] with n hn hin hjn
    intro k
    by_cases hcut : if strict then 2*k<ns n else 2*k≤ns n
    · have hkhalf : 2*k≤ns n := by
        cases strict with
        | false => exact hcut
        | true => exact le_of_lt hcut
      have hk : k<ns n+1 := by omega
      have hd : edgeIndex (ns n+1) k=k+1 := by dsimp only [edgeIndex]; omega
      have h := hn (i n) (j n) hin hjn ⟨k,hk⟩
      simpa only [gramHalfTerm,ite_eq_left hcut,gramSummandAt,dite_eq_left hk,
        abs_mul,abs_of_pos (show (0:ℝ)<(ns n:ℝ)+1 by positivity),hd,Nat.cast_add,Nat.cast_one] using h
    · rw [gramHalfTerm,ite_eq_right hcut,abs_zero]
      exact add_nonneg (by positivity) (hε (ns n))
  · intro k
    exact gramHalfTerm_limit strict ha hb k ns hns i j hi hj ht hs hit hjs

end
end jacobi.Comparison
