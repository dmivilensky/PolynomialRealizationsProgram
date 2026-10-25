import polyak.Levels.Chart.AngleGap

/-! Exact cosine coordinates of every source gap, including K=2. -/
noncomputable section
namespace polyak.Levels.Chart
open Set

def boundaryAngle (K : ℕ) : ℝ := 2*Real.pi/(K:ℝ)
def boundaryCosine (K : ℕ) : ℝ := Real.cos (boundaryAngle K)

theorem boundaryAngle_mem {K : ℕ} (hK : 2≤K) : boundaryAngle K∈Ioc (0:ℝ) Real.pi := by
  have hk : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hk2 : (2:ℝ)≤K := by exact_mod_cast hK
  refine ⟨div_pos (by positivity [Real.pi_pos]) hk,?_⟩
  apply (div_le_iff₀ hk).mpr
  nlinarith [Real.pi_pos]

theorem boundaryAngle_succ_mem {K : ℕ} (hK : 2≤K) :
    boundaryAngle (K+1)∈Ioo (0:ℝ) Real.pi := by
  have hp := boundaryAngle_mem (K:=K+1) (by omega)
  refine ⟨hp.1,?_⟩
  have hk : (0:ℝ)<K+1 := by positivity
  unfold boundaryAngle
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<(K+1:ℕ))).mpr
  push_cast
  have hk2 : (2:ℝ)≤K := by exact_mod_cast hK
  nlinarith [Real.pi_pos]

theorem boundaryAngle_succ_lt {K : ℕ} (hK : 2≤K) : boundaryAngle (K+1)<boundaryAngle K := by
  have hk : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  unfold boundaryAngle
  apply div_lt_div_of_pos_left (by positivity [Real.pi_pos]) hk
  norm_cast
  omega

theorem boundaryCosine_lt_succ {K : ℕ} (hK : 2≤K) : boundaryCosine K<boundaryCosine (K+1) :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (boundaryAngle_succ_mem hK).1.le
    (boundaryAngle_mem hK).2 (boundaryAngle_succ_lt hK)

theorem boundaryCosine_succ_lt_one {K : ℕ} (hK : 2≤K) : boundaryCosine (K+1)<1 := by
  have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by rfl)
    (boundaryAngle_succ_mem hK).2.le (boundaryAngle_succ_mem hK).1
  simpa only [boundaryCosine,Real.cos_zero] using hh

theorem boundaryCosine_ge_neg_one (K : ℕ) : -1≤boundaryCosine K := Real.neg_one_le_cos _

@[simp] theorem boundaryCosine_two : boundaryCosine 2= -1 := by
  unfold boundaryCosine boundaryAngle
  norm_num [Real.cos_pi]

theorem cos_window_iff {K : ℕ} (hK : 2≤K) {ω : ℝ} (hω : ω∈Icc (0:ℝ) Real.pi) :
    boundaryCosine K<Real.cos ω ∧ Real.cos ω<boundaryCosine (K+1) ↔
      boundaryAngle (K+1)<ω ∧ ω<boundaryAngle K := by
  have hleft := Real.strictAntiOn_cos.lt_iff_gt
    ⟨(boundaryAngle_mem hK).1.le,(boundaryAngle_mem hK).2⟩ hω
  have hright := Real.strictAntiOn_cos.lt_iff_gt hω
    ⟨(boundaryAngle_succ_mem hK).1.le,(boundaryAngle_succ_mem hK).2.le⟩
  change (Real.cos (boundaryAngle K)<Real.cos ω ∧
    Real.cos ω<Real.cos (boundaryAngle (K+1))) ↔ _
  rw [hleft,hright,and_comm]

end polyak.Levels.Chart
