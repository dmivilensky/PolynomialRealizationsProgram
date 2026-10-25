import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

/-! Exact quadratic Taylor bounds on closed intervals, including their endpoints. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set

theorem quadratic_taylor {a b z x:ℝ} {f:ℝ→ℝ}
    (hf:∀y∈Icc a b,ContDiffAt ℝ 2 f y) (hz:z∈Icc a b) (hx:x∈Icc a b)
    (hne:z≠x) (hzero:f z=0) (hderiv:deriv f z=0) :
    ∃y∈uIoo z x,f x=iteratedDeriv 2 f y*(x-z)^2/2 := by
  have hsub:uIcc z x⊆Icc a b:=uIcc_subset_Icc hz hx
  have hc:ContDiffOn ℝ (1+1) f (uIcc z x):=fun y hy=>(hf y (hsub hy)).contDiffWithinAt
  obtain ⟨y,hy,he⟩:=taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hne hc
  have hdiff:iteratedDerivWithin 1 f (uIcc z x) z=deriv f z:=by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      ((hf z hz).of_le (by norm_num)) (left_mem_uIcc)]
    simp
  simp only [taylorWithinEval_succ,taylor_within_zero_eval,hdiff,hzero,hderiv,
    zero_add,smul_zero,sub_zero] at he
  norm_num at he
  exact ⟨y,hy,he⟩

theorem quadratic_upper_bound {a b z x M:ℝ} {f:ℝ→ℝ}
    (hf:∀y∈Icc a b,ContDiffAt ℝ 2 f y) (hz:z∈Icc a b) (hx:x∈Icc a b)
    (hzero:f z=0) (hderiv:deriv f z=0)
    (hbound:∀y∈uIcc z x,iteratedDeriv 2 f y≤M) :
    f x≤M*(x-z)^2/2 := by
  by_cases he:z=x
  · subst x
    simp [hzero]
  obtain ⟨y,hy,hform⟩:=quadratic_taylor hf hz hx he hzero hderiv
  rw [hform]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound y (Ioo_subset_Icc_self hy)) (sq_nonneg _)) (by norm_num)

theorem quadratic_abs_bound {a b z x M:ℝ} {f:ℝ→ℝ}
    (hf:∀y∈Icc a b,ContDiffAt ℝ 2 f y) (hz:z∈Icc a b) (hx:x∈Icc a b)
    (hzero:f z=0) (hderiv:deriv f z=0)
    (hbound:∀y∈Icc a b,|iteratedDeriv 2 f y|≤M) :
    |f x|≤M*(x-z)^2/2 := by
  by_cases he:z=x
  · subst x
    simp [hzero]
  obtain ⟨y,hy,hform⟩:=quadratic_taylor hf hz hx he hzero hderiv
  rw [hform,abs_div,abs_mul,abs_pow,sq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound y (uIcc_subset_Icc hz hx (Ioo_subset_Icc_self hy)))
      (sq_nonneg _)) (by norm_num)

end polyak.ModeLocking.Analysis
