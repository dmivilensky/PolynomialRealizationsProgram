import polyak.General.IQC.SequenceSpace

/-! Article: Appendix D, causal execution of a stable strictly proper filter.
A summable real impulse kernel gives an operator on unrestricted sequences;
its ℓ² gain on every finite prefix is bounded by its ℓ¹ coefficient mass. -/
noncomputable section
namespace polyak.General.IQC
open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def delay (m : ℕ) (x : ℕ → E) (k : ℕ) : E := if m≤k then x (k-m) else 0

omit [NormedSpace ℝ E] in
theorem delay_add (m : ℕ) (x y : ℕ → E) : delay m (x+y)=delay m x+delay m y := by
  funext k
  by_cases hm : m≤k <;> simp [delay,hm]

theorem delay_smul (m : ℕ) (r : ℝ) (x : ℕ → E) : delay m (r • x)=r • delay m x := by
  funext k
  by_cases hm : m≤k <;> simp [delay,hm]

omit [NormedSpace ℝ E] in
theorem prefixNorm_delay (m : ℕ) (x : ℕ → E) (N : ℕ) :
    prefixNorm (delay m x) N=prefixNorm x (N-m) := by
  apply (sq_eq_sq₀ (prefixNorm_nonneg _ _) (prefixNorm_nonneg _ _)).mp
  rw [prefixNorm_sq,prefixNorm_sq]
  by_cases hm : m≤N
  · conv_lhs => rw [show N=m+(N-m) by omega,sum_range_add]
    have hz : (∑ k∈range m,‖delay m x k‖^2)=0:=by
      apply sum_eq_zero
      intro k hk
      simp [delay,show ¬m≤k by have hh:=mem_range.mp hk; omega]
    rw [hz,zero_add]
    apply sum_congr rfl
    intro k _
    simp [delay]
  · have hz : N-m=0:=by omega
    rw [hz,sum_range_zero]
    apply sum_eq_zero
    intro k hk
    simp [delay,show ¬m≤k by have hh:=mem_range.mp hk; omega]

def convolution (h : ℕ → ℝ) : (ℕ → E) →ₗ[ℝ] (ℕ → E) where
  toFun x k:=∑ m∈range (k+1),h m • delay m x k
  map_add' x y:=by
    funext k
    simp only [delay_add,Pi.add_apply,smul_add,sum_add_distrib]
  map_smul' r x:=by
    funext k
    change (∑ m∈range (k+1),h m • delay m (r • x) k)=
      r • (∑ m∈range (k+1),h m • delay m x k)
    rw [Finset.smul_sum]
    apply sum_congr rfl
    intro m _
    rw [delay_smul]
    change h m • (r • delay m x k)=r • (h m • delay m x k)
    exact smul_comm _ _ _

theorem convolution_strictCausal {h : ℕ → ℝ} (h0 : h 0=0) :
    StrictCausal (convolution (E:=E) h) := by
  intro k x y hxy
  change (∑ m∈range (k+1),h m • delay m x k)=∑ m∈range (k+1),h m • delay m y k
  apply sum_congr rfl
  intro m _
  by_cases hm0 : m=0
  · subst m
    simp [h0]
  · by_cases hm : m≤k
    · simp only [delay,ite_eq_left hm]
      rw [hxy (k-m) (by omega)]
    · simp [delay,hm]

def prefixLinear (N : ℕ) : (ℕ → E) →ₗ[ℝ] PiLp 2 (fun _ : Fin N => E) where
  toFun x:=WithLp.toLp 2 (fun k => x k)
  map_add' _ _:=rfl
  map_smul' _ _:=by
    apply WithLp.ofLp_injective 2
    rfl

theorem prefixNorm_finset_sum {I : Type*} (s : Finset I) (f : I → ℕ → E) (N : ℕ) :
    prefixNorm (∑ i∈s,f i) N≤∑ i∈s,prefixNorm (f i) N := by
  change ‖prefixLinear N (∑ i∈s,f i)‖≤∑ i∈s,‖prefixLinear N (f i)‖
  rw [map_sum]
  exact norm_sum_le _ _

theorem convolution_prefix {h : ℕ → ℝ} (x : ℕ → E) {N k : ℕ} (hk : k<N) :
    convolution h x k=(∑ m∈range N,h m • delay m x) k := by
  simp only [convolution,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,Pi.smul_apply]
  apply sum_subset (range_mono (show k+1≤N by omega))
  intro m _ hm
  have hmk : ¬ m ≤ k := by
    have hh : ¬ m < k+1 := by simpa only [mem_range] using hm
    omega
  simp [delay,hmk]

theorem convolution_prefix_gain {h : ℕ → ℝ} (hh : Summable (fun m => |h m|))
    (x : ℕ → E) (N : ℕ) :
    prefixNorm (convolution h x) N≤(∑' m,|h m|)*prefixNorm x N := by
  calc
    _=prefixNorm (∑ m∈range N,h m • delay m x) N:=
      prefixNorm_congr (fun k hk => convolution_prefix x hk)
    _≤∑ m∈range N,prefixNorm (h m • delay m x) N:=prefixNorm_finset_sum _ _ N
    _=∑ m∈range N,|h m| * prefixNorm x (N-m):=by
      apply sum_congr rfl
      intro m _
      rw [prefixNorm_smul,prefixNorm_delay]
    _≤∑ m∈range N,|h m| * prefixNorm x N:=by
      apply sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (prefixNorm_mono (Nat.sub_le _ _)) (abs_nonneg _)
    _=(∑ m∈range N,|h m|)*prefixNorm x N:=by rw [sum_mul]
    _≤(∑' m,|h m|)*prefixNorm x N:=mul_le_mul_of_nonneg_right
      (hh.sum_le_tsum (range N) (fun m _ => abs_nonneg _)) (prefixNorm_nonneg _ _)

end polyak.General.IQC
