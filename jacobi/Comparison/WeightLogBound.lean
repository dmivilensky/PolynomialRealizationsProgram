import jacobi.Comparison.WeightLogFactors
import jacobi.Finite.TwoEdgeLogRows
import jacobi.Finite.HarmonicRows

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The original finite relative gap product has the full printed logarithm
bound at every spectral index. The previously proved continuum row
majorant controls the folded edges; the exact harmonic row controls the
growing bulk. Every original spectral and frequency input is discharged.
Use: the target/support probability-ratio bounds and their normalization error follow by exponentiation of this same actual finite product; its summable edge tails feed the two-edge Gram limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Finite
open scoped Topology

/-- The actual original relative gap products obey the complete printed uniform two-edge logarithm estimate.
Use: the target/support probability-ratio bounds and their normalization error follow by exponentiation of this same actual finite product; its summable edge tails feed the two-edge Gram limit.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the logarithm is the finite sum of the genuine positive gap-factor logarithms. Sum their independently proved quantitative majorants. The inverse-square row folds onto the earlier continuum p-series majorant with multiplicity at most two; the bulk row is bounded by two harmonic prefixes. The original frequency is at least half the actual dimension. Finally absorb 1+log n into log n beyond dimension two and choose one common positive constant. -/
theorem comparisonWeight_log_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),
      |log (relativeGapProduct a b ha hb n i)|≤
        C*(1/(jacobi.Jacobi.edgeIndex (n+1) i.val:ℝ)^2+log ((n:ℝ)+1)/((n:ℝ)+1)^2) := by
  -- All row estimates are for the actual finite node family and its exact omitted diagonal.
  obtain ⟨C,hC,hbound⟩ := comparisonGap_log_majorant ha hb
  let Z : ℝ := ∑'j:ℕ,1/(j+1:ℝ)^2
  let K : ℝ := 2*(1+8*Z)
  let T : ℝ := 1+1/log 2
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  have hK : 0<K := by dsimp [K]; positivity
  have hlog2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hT : 0<T := by dsimp [T]; positivity
  refine ⟨C*(K+8*T),by positivity,?_⟩
  filter_upwards [hbound,(tendsto_add_atTop_nat 1).eventually (jacobi.Jacobi.frequency_degree_comparison a b),
    eventually_ge_atTop (1:ℕ)] with n hn hfreq hn1
  intro i
  let N : ℝ := (n:ℝ)+1
  let F := jacobi.Jacobi.frequency a b (n+1)
  let di : ℝ := jacobi.Jacobi.edgeIndex (n+1) i.val
  let A (j:Fin (n+1)) := (1/di^2+1/(jacobi.Jacobi.edgeIndex (n+1) j.val:ℝ)^2)/
    (|(i.val:ℝ)-j.val| *(jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ))
  let B (j:Fin (n+1)) := (di+(jacobi.Jacobi.edgeIndex (n+1) j.val:ℝ))/
    (|(i.val:ℝ)-j.val| *(jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ))
  have hN : 0<N := by dsimp [N]; positivity
  have hN2 : (2:ℝ)≤N := by dsimp [N]; exact_mod_cast (show 2≤n+1 by omega)
  have hF : 0<F := hfreq.1
  have hFN : N≤2*F := by simpa only [N,Nat.cast_add,Nat.cast_one] using hfreq.2.1
  have hdi : 0<di := by
    dsimp [di]
    exact_mod_cast (show 0< jacobi.Jacobi.edgeIndex (n+1) i.val by dsimp [jacobi.Jacobi.edgeIndex]; omega)
  have hrowsA : (∑j∈univ.erase i,A j)≤K/di^2 := twoEdge_error_row i
  have hrowsB : (∑j∈univ.erase i,B j)≤2*(1+log N) := by
    simpa only [N,Nat.cast_add,Nat.cast_one] using twoEdge_harmonic_row i
  have hlogN : log 2≤log N := log_le_log (by norm_num) hN2
  have hL : 1+log N≤T*log N := by
    have h := div_le_div_of_nonneg_right hlogN hlog2.le
    rw [div_self hlog2.ne'] at h
    calc
      _ ≤ log N/log 2+log N := add_le_add h le_rfl
      _ = _ := by dsimp [T]; ring
  have hterm (j:Fin (n+1)) (hj:j∈univ.erase i) :
      |log (|jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val|/
        |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|)|≤
        C*(A j+B j/F^2) := by
    exact (hn i j (mem_erase.mp hj).1.symm).trans_eq (by
      dsimp [A,B,di,F]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring)
  have hlog : |log (relativeGapProduct a b ha hb n i)|≤C*(K/di^2+2*(1+log N)/F^2) := by
    rw [relativeGapProduct_log_sum]
    calc
      _ ≤ ∑j∈univ.erase i,|log (|jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val|/
          |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑j∈univ.erase i,C*(A j+B j/F^2) := sum_le_sum hterm
      _ = C*((∑j∈univ.erase i,A j)+(∑j∈univ.erase i,B j)/F^2) := by
        rw [← mul_sum,sum_add_distrib,← sum_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hrowsA
        (div_le_div_of_nonneg_right hrowsB (sq_nonneg F))) hC.le
  have hbulk : 2*(1+log N)/F^2≤8*T*log N/N^2 := by
    have hp : N^2≤4*F^2 := by nlinarith
    have hLpos : 0≤1+log N := by linarith
    calc
      _ ≤ 8*(1+log N)/N^2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hF) (sq_pos_of_pos hN)).mpr
        have h := mul_le_mul_of_nonneg_left hp (show 0≤2*(1+log N) by positivity)
        nlinarith only [h]
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hL]) (sq_nonneg N)
  have hsum : K/di^2+8*T*log N/N^2≤(K+8*T)*(1/di^2+log N/N^2) := by
    have hp₁ := mul_nonneg hK.le (div_nonneg (hlog2.le.trans hlogN) (sq_nonneg N))
    have hp₂ := mul_nonneg (show 0≤8*T by positivity) (show 0≤1/di^2 by positivity)
    calc
      _ ≤ (K/di^2+8*T*log N/N^2)+(K*(log N/N^2)+8*T*(1/di^2)) :=
        le_add_of_nonneg_right (add_nonneg hp₁ hp₂)
      _ = _ := by ring
  calc
    _ ≤ C*(K/di^2+2*(1+log N)/F^2) := hlog
    _ ≤ C*(K/di^2+8*T*log N/N^2) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hbulk) hC.le
    _ ≤ C*((K+8*T)*(1/di^2+log N/N^2)) := mul_le_mul_of_nonneg_left hsum hC.le
    _ = _ := by ring

end
end jacobi.Comparison
