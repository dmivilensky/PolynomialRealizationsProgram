import krylov.Tensor.BinaryRFC

/-!
Article: main_krylov, thm:Fplanar, stability of the actual C_Y coefficient.
Use: transport the genuine RFC-F supremum under the O(e) true-minimizer
reference-ratio drift. Source: the proved true coefficient disks and the
uniform Lipschitz bound for the original full-ball objective.
-/
namespace krylov.Tensor.BinaryCubic
noncomputable section
open Set

/-- The actual full-ball RFC-F objective is uniformly 2-Lipschitz in its
real reference ratio. Article: main_krylov, thm:Fplanar. -/
theorem rfcObjective_lipschitz {t : BinaryCubic} (ht : t.InBall) (r s : ℝ) :
    |rfcObjective r t-rfcObjective s t|≤2*|r-s| := by
  have hd := (coefficient_disks ht).2
  have hC : |t.t2|≤1 := by nlinarith only [hd,sq_nonneg t.t1,sq_abs t.t2,abs_nonneg t.t2]
  have hW : Real.sqrt (4*t.t1^2+t.t2^2)≤2 := by
    have hs := Real.sq_sqrt (by positivity : 0≤4*t.t1^2+t.t2^2)
    nlinarith only [hs,hd,sq_nonneg t.t2,Real.sqrt_nonneg (4*t.t1^2+t.t2^2)]
  unfold rfcObjective
  rw [←sub_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ |(t.t1+r*t.t2)-(t.t1+s*t.t2)| *Real.sqrt (4*t.t1^2+t.t2^2) :=
      mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) (Real.sqrt_nonneg _)
    _ = |r-s| *|t.t2| *Real.sqrt (4*t.t1^2+t.t2^2) := by
      rw [show (t.t1+r*t.t2)-(t.t1+s*t.t2)=(r-s)*t.t2 by ring,abs_mul]
    _ ≤ |r-s| *1*2 := mul_le_mul
      (mul_le_mul_of_nonneg_left hC (abs_nonneg _)) hW (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

/-- The genuine supremum over the whole original cubic ball is globally
2-Lipschitz. Article: main_krylov, thm:Fplanar, C_Y reference stability. -/
theorem rfcWorst_lipschitz (r s : ℝ) : |rfcWorst r-rfcWorst s|≤2*|r-s| := by
  have horder (x y : ℝ) : rfcWorst x≤rfcWorst y+2*|x-y| := by
    apply csSup_le ⟨2,two_mem_rfcValues x⟩
    rintro v ⟨t,ht,rfl⟩
    have hh := (abs_le.mp (rfcObjective_lipschitz ht x y)).2
    have hy : rfcObjective y t≤rfcWorst y := le_csSup (rfcValues_bddAbove y) ⟨t,ht,rfl⟩
    linarith only [hh,hy]
  apply abs_le.mpr
  have hs := horder s r
  rw [abs_sub_comm s r] at hs
  exact ⟨by linarith only [hs],by linarith only [horder r s]⟩

/-- The actual C_Y coefficient is Lipschitz on every bounded ratio interval,
with an explicit common constant. Article: main_krylov, thm:Fplanar. -/
theorem modelMetricCoefficient_lipschitz_on (R : ℝ) (hR : 0≤R)
    (r s : ℝ) (hr : |r|≤R) (hs : |s|≤R) :
    |modelMetricCoefficient r-modelMetricCoefficient s|≤
      (2*Real.sqrt (1+R^2)+2*R)*|r-s| := by
  have hWr : |rfcWorst r|≤2*Real.sqrt (1+R^2) := by
    rw [abs_of_nonneg (by have hh := (rfcWorst_bounds r).1; linarith only [hh])]
    have hsq : r^2≤R^2 := by nlinarith only [sq_abs r,hr,mul_self_le_mul_self (abs_nonneg r) hr]
    exact (rfcWorst_bounds r).2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith only [hsq])) (by norm_num))
  have he : modelMetricCoefficient r-modelMetricCoefficient s=
      (r-s)*rfcWorst r+s*(rfcWorst r-rfcWorst s) := by unfold modelMetricCoefficient; ring
  rw [he]
  calc
    _ ≤ |(r-s)*rfcWorst r|+|s*(rfcWorst r-rfcWorst s)| := abs_add_le _ _
    _ = |r-s| *|rfcWorst r|+|s| *|rfcWorst r-rfcWorst s| := by rw [abs_mul,abs_mul]
    _ ≤ |r-s| *(2*Real.sqrt (1+R^2))+R*(2*|r-s|) := add_le_add
      (mul_le_mul_of_nonneg_left hWr (abs_nonneg _))
      (mul_le_mul hs (rfcWorst_lipschitz r s) (abs_nonneg _) hR)
    _ = _ := by ring

end
end krylov.Tensor.BinaryCubic
