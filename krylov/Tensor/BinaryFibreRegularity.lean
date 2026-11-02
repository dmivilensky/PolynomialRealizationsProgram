import krylov.Tensor.BinaryShear
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Article: main_krylov, thm:Fplanar.
Use: complete the local Lipschitz and small-r asymptotic analysis of the
actual all-chord function-value information coefficient M_F.
Source: the proved scaled shear of the genuine binary cubic ball. A
nonsharp numerical regularity constant suffices; the limiting 1/3 is exact.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- A uniform one-sided Lipschitz estimate for the actual fibre coefficient
on every bounded parameter interval.
Article: main_krylov, thm:Fplanar, local Lipschitz regularity of M_F. -/
theorem fibreMinimax_sub_le (r r' R : ℝ) (hR : 0≤R) (hr : |r|≤R) (hr' : |r'|≤R) :
    fibreMinimax r-fibreMinimax r'≤48*(1+R)*(1+6*R)*|r-r'| := by
  let D := |r-r'|
  have hD : 0≤D := abs_nonneg _
  have hDle : D≤2*R := (abs_sub r r').trans (by linarith)
  have hM : fibreMinimax r'≤4*(1+R) :=
    (fibreMinimax_bounds r').2.trans (by linarith)
  have hfac : 12*D+36*D^2≤(12+72*R)*D := by
    nlinarith [mul_nonneg hD (by linarith : 0≤2*R-D)]
  calc
    fibreMinimax r-fibreMinimax r' ≤ (12*D+36*D^2)*fibreMinimax r' := by
      have h := fibreMinimax_shear r r'
      change fibreMinimax r≤(1+6*D)^2*fibreMinimax r' at h
      nlinarith
    _ ≤ ((12+72*R)*D)*(4*(1+R)) :=
      mul_le_mul hfac hM (fibreMinimax_bounds r').1 (by positivity)
    _ = 48*(1+R)*(1+6*R)*|r-r'| := by dsimp only [D];ring

/-- The genuine minimax coefficient is quantitatively Lipschitz on bounded
sets, including across zero.
Article: main_krylov, thm:Fplanar, local Lipschitz regularity of M_F. -/
theorem fibreMinimax_abs_sub_le (r r' R : ℝ) (hR : 0≤R) (hr : |r|≤R) (hr' : |r'|≤R) :
    |fibreMinimax r-fibreMinimax r'|≤48*(1+R)*(1+6*R)*|r-r'| := by
  apply abs_le.mpr
  constructor
  · have h := fibreMinimax_sub_le r' r R hR hr' hr
    rw [abs_sub_comm r' r] at h
    linarith
  · exact fibreMinimax_sub_le r r' R hR hr hr'

/-- The quantitative estimate is a genuine Lipschitz predicate on every
bounded interval. Article: main_krylov, thm:Fplanar. -/
theorem fibreMinimax_lipschitzOnWith (R : ℝ) (hR : 0≤R) :
    LipschitzOnWith (Real.toNNReal (48*(1+R)*(1+6*R))) fibreMinimax (Set.Icc (-R) R) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro r hr r' hr'
  have hrabs : |r|≤R := abs_le.mpr ⟨hr.1,hr.2⟩
  have hrabs' : |r'|≤R := abs_le.mpr ⟨hr'.1,hr'.2⟩
  simp only [Real.dist_eq]
  rw [Real.coe_toNNReal _ (by positivity)]
  exact fibreMinimax_abs_sub_le r r' R hR hrabs hrabs'

/-- An explicit neighborhood estimate with the exact limiting constant 1/3.
Article: main_krylov, thm:Fplanar, M_F(r)=1/3+O(r). -/
theorem fibreMinimax_near_zero {r : ℝ} (hr : |r|≤1) :
    |fibreMinimax r-1/3|≤672*|r| := by
  have h := fibreMinimax_abs_sub_le r 0 1 (by norm_num) hr (by norm_num)
  norm_num only [fibreMinimax_zero,sub_zero,mul_one,mul_zero,add_zero] at h
  norm_num at h ⊢
  exact h

/-- The actual all-chord minimax has the stated sharp leading asymptotic.
Article: main_krylov, thm:Fplanar, M_F(r)=1/3+O(r) as r tends to zero.
Proof: the quantitative local estimate is valid in a true neighborhood,
with an explicit finite constant, and its limit is the proved sharp value. -/
theorem fibreMinimax_isBigO :
    (fun r : ℝ => fibreMinimax r-1/3) =O[𝓝 0] (fun r : ℝ => r) := by
  apply Asymptotics.IsBigO.of_bound 672
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with r hr
  have habs : |r|<1 := by simpa [Metric.mem_ball,Real.dist_eq] using hr
  simpa only [Real.norm_eq_abs] using fibreMinimax_near_zero habs.le

/-- The function-value minimax coefficient converges to the exact value 1/3.
Article: main_krylov, thm:Fplanar, M_F(r)→1/3. -/
theorem fibreMinimax_tendsto : Tendsto fibreMinimax (𝓝 0) (𝓝 (1/3)) := by
  have hz : Tendsto (fun r : ℝ => fibreMinimax r-1/3) (𝓝 0) (𝓝 0) :=
    fibreMinimax_isBigO.trans_tendsto tendsto_id
  have h := hz.add_const (1/3 : ℝ)
  simpa only [sub_add_cancel,zero_add] using h

end
end krylov.Tensor.BinaryCubic
