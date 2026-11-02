import jacobi.Jacobi.StandardKernelLimit
import jacobi.Analysis.PositiveSequenceBounds

/-!
Global bounds for the genuine standard Jacobi Green matrices.
The actual norm power law includes every finite initial index. Positive
endpoint exponents compare every earlier endpoint with a later one, and
each true Green tail summand is consequently bounded by one common constant.
Use: dominated mesh convergence for the energy and initial flow derivative
includes the singular corner without assuming a separate boundary estimate.
Article: jacobi, Theorem 5.4.
Article role: the global diagonal bound controlling the omitted boundary cells.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Filter Set jacobi.Analysis jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual endpoint squares have uniform two-sided power bounds,
including degree zero. The positive shift avoids a zero power base.
Article: jacobi, Theorem 5.4.
-/
theorem standardEndpointSquare_bounds {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ i : ℕ,
      c*((i:ℝ)+1)^(2*a+1)≤standardEndpointSquare a b i ∧
        standardEndpointSquare a b i≤C*((i:ℝ)+1)^(2*a+1) := by
  have hr : Tendsto (fun k : ℕ => (k:ℝ)/((k+1:ℕ):ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_zero] using shifted_nat_ratio 0 1
  have h := power_mesh_limit _ (standardEndpointSquare_power_limit ha hb)
    (by norm_num : (0:ℝ)<1) (tendsto_add_atTop_nat 1) hr
  simp only [one_rpow,mul_one,Nat.cast_add,Nat.cast_one] at h
  obtain ⟨c,C,hc,hC,hbound⟩ := positive_sequence_bounds
    (fun i => div_pos (standardEndpointSquare_pos ha hb i) (rpow_pos_of_pos (by positivity) _))
    (standardEndpointConstant_pos ha hb) h
  refine ⟨c,C,hc,hC,fun i => ?_⟩
  have hp : 0<((i:ℝ)+1)^(2*a+1) := rpow_pos_of_pos (by positivity) _
  exact ⟨(le_div_iff₀ hp).mp (hbound i).1,(div_le_iff₀ hp).mp (hbound i).2⟩

/-- Every earlier endpoint square is bounded by a common multiple of
every later conductance. This is the finite bound behind both the
diagonal energy and the full off-diagonal flow derivative estimates.
Article: jacobi, Theorem 5.4.
-/
theorem standard_endpoint_conductance_bound {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    ∃ K : ℝ,0<K ∧ ∀ i l : ℕ,i≤l →
      standardEndpointSquare a b i≤K*standardConductance a b l := by
  have ha' : -1<a := by linarith
  obtain ⟨c,C,hc,hC,hU⟩ := standardEndpointSquare_bounds ha' hb
  obtain ⟨v,V,hv,_,hF⟩ := positive_sequence_bounds (standardForward_pos ha' hb)
    (by norm_num : (0:ℝ)<1/2) (standardForward_limit a b)
  let K := C/(c*v)
  have hK : 0<K := div_pos hC (mul_pos hc hv)
  refine ⟨K,hK,fun i l hil => ?_⟩
  have hp : ((i:ℝ)+1)^(2*a+1)≤((l:ℝ)+1)^(2*a+1) :=
    rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hil 1) (by linarith)
  have hcond : (c*v)*((l:ℝ)+1)^(2*a+1)≤standardConductance a b l := by
    have h := mul_le_mul (hU l).1 (hF l).1 hv.le (standardEndpointSquare_pos ha' hb l).le
    simpa only [standardConductance,mul_assoc,mul_comm,mul_left_comm] using h
  have hmul := mul_le_mul_of_nonneg_left hcond hK.le
  have hcancel : K*((c*v)*((l:ℝ)+1)^(2*a+1))=C*((l:ℝ)+1)^(2*a+1) := by
    dsimp [K]
    field_simp [hc.ne',hv.ne']
  rw [hcancel] at hmul
  exact ((hU i).2.trans (mul_le_mul_of_nonneg_left hp hC.le)).trans hmul

/-- Every actual extended Green entry is bounded by a common constant
times the matrix dimension. The proof bounds each conductance summand;
it handles the zero extension and all small indices at the same time.
Article: jacobi, Theorem 5.4.
-/
theorem standardGreenTail_bound {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    ∃ K : ℝ,0<K ∧ ∀ N i j : ℕ,standardGreenTail a b N i j≤K*(N:ℝ) := by
  have ha' : -1<a := by linarith
  obtain ⟨K,hK,hbound⟩ := standard_endpoint_conductance_bound ha hb
  refine ⟨K,hK,fun N i j => ?_⟩
  calc
    standardGreenTail a b N i j=∑ l∈Finset.range N,if max i j≤l then
        standardEndpoint a b i*standardEndpoint a b j/standardConductance a b l else 0 := by
      unfold standardGreenTail
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> simp only [mul_zero,div_eq_mul_inv]
    _ ≤ ∑ l∈Finset.range N,K := by
      apply Finset.sum_le_sum
      intro l _
      split_ifs with hl
      · apply (div_le_iff₀ (standardConductance_pos ha' hb l)).mpr
        have hi := hbound i l ((le_max_left _ _).trans hl)
        have hj := hbound j l ((le_max_right _ _).trans hl)
        rw [← standardEndpoint_sq ha' hb i] at hi
        rw [← standardEndpoint_sq ha' hb j] at hj
        nlinarith [sq_nonneg (standardEndpoint a b i-standardEndpoint a b j)]
      · exact hK.le
    _ = K*(N:ℝ) := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

/-- The genuine dimension-normalized Green entries are uniformly
bounded over every matrix size and every natural pair of indices.
Article: jacobi, Theorem 5.4.
-/
theorem standardGreenTail_normalized_bound {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    ∃ K : ℝ,0<K ∧ ∀ N i j : ℕ,|standardGreenTail a b N i j/(N:ℝ)|≤K := by
  obtain ⟨K,hK,hbound⟩ := standardGreenTail_bound ha hb
  refine ⟨K,hK,fun N i j => ?_⟩
  by_cases hN : N=0
  · simp only [hN,Nat.cast_zero,div_zero,abs_zero]
    exact hK.le
  · have hnR : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [abs_of_nonneg (div_nonneg (standardGreenTail_nonneg (by linarith : -1<a) hb N i j) hnR.le)]
    exact (div_le_iff₀ hnR).mpr (hbound N i j)

end
end jacobi.Jacobi
