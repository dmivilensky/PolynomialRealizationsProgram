import polyak.Global.Kernels.GainStrict
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-! Uniform positive loss at high real frequencies, with the actual bump. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function Filter Complex
open scoped Topology ENNReal NNReal

theorem psi_characteristic_tendsto :
    Tendsto (charFun psiMeasure) (cocompact ℝ) (𝓝 0) := by
  have ha : (-(1/(2*Real.pi)):ℝ) ≠ 0 := by exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  have hh := (Real.tendsto_integral_exp_smul_cocompact (fun x:ℝ=>(psi x:ℂ))).comp
    (tendsto_cocompact_mul_left₀ ha)
  convert hh using 1
  ext ξ
  rw [charFun_apply_real,integral_psiMeasure]
  congr 1
  ext x
  simp only [Real.fourierChar_apply,_root_.Circle.smul_def,
    Complex.real_smul]
  rw [mul_comm (psi x:ℂ)]
  congr 1
  push_cast
  field_simp

theorem psiHat_tendsto : Tendsto psiHat (cocompact ℝ) (𝓝 0) := by
  exact (Complex.continuous_re.tendsto 0).comp psi_characteristic_tendsto

theorem phiHat_tendsto : Tendsto phiHat (cocompact ℝ) (𝓝 0) := by
  change Tendsto (fun ξ=>psiHat ξ^2) _ _
  simpa only [zero_pow (by norm_num:2≠0)] using psiHat_tendsto.pow 2

/-- A genuine uniform lower bound on the entire unbounded high-frequency region. -/
theorem phiHat_gap_large : ∃c:ℝ,0<c ∧ ∀ξ:ℝ,2*Real.pi≤|ξ|→c≤1-phiHat ξ := by
  have he := (Metric.tendsto_nhds.mp phiHat_tendsto) (1/2) (by norm_num)
  obtain ⟨S,hS,hbound⟩ := Filter.mem_cocompact.mp he
  obtain ⟨R,hR⟩ := hS.isBounded.subset_closedBall (0:ℝ)
  let A := max (2*Real.pi) (R+1)
  let S' : Set ℝ := {ξ | 2*Real.pi≤|ξ| ∧ |ξ|≤A}
  have hscompact : IsCompact S' := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℝ) A)
      ((isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const))
    intro ξ hξ
    change 2*Real.pi≤|ξ| ∧ |ξ|≤A at hξ
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hξ.2
  have hsnonempty : S'.Nonempty := by
    refine ⟨2*Real.pi,?_,?_⟩
    · rw [abs_of_pos Real.two_pi_pos]
    · rw [abs_of_pos Real.two_pi_pos]
      exact le_max_left _ _
  obtain ⟨ξ₀,hξ₀,hmin⟩ := hscompact.exists_isMinOn hsnonempty
    ((show Continuous (fun ξ:ℝ=>1-phiHat ξ) from continuous_const.sub continuous_phiHat).continuousOn)
  change 2*Real.pi≤|ξ₀| ∧ |ξ₀|≤A at hξ₀
  have hc : 0<1-phiHat ξ₀ := sub_pos.mpr (phiHat_lt_one (by
    intro hzero
    rw [hzero,abs_zero] at hξ₀
    linarith [hξ₀.1,Real.pi_pos]))
  refine ⟨min (1/2) (1-phiHat ξ₀),lt_min (by norm_num) hc,?_⟩
  intro ξ hξ
  by_cases hsmall : |ξ|≤A
  · exact (min_le_right _ _).trans (hmin ⟨hξ,hsmall⟩)
  · have hnot : ξ∉S := by
      intro hm
      have hb := hR hm
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
      have hRA : R<A := (lt_add_one R).trans_le (le_max_right _ _)
      exact hsmall (hb.trans hRA.le)
    have hh := hbound hnot
    change dist (phiHat ξ) 0<1/2 at hh
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (phiHat_mem ξ).1] at hh
    exact (min_le_left _ _).trans (by linarith)

end polyak.Global.Kernels
