import nesterov.Faithful.ScaledSymbol
import nesterov.Faithful.PolynomialPositive
import nesterov.Faithful.FamilySmooth

/-! Extraction of the constant and linear ξ-coefficients from two slow rays. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology

theorem one_sub_cos_ratio_limit :
    Tendsto (fun ε : ℝ=>(1-Real.cos ε)/ε^2) (𝓝[>] (0:ℝ)) (𝓝 (1/2:ℝ)) := by
  obtain ⟨E,hE,he0,_,he⟩ := exists_circle_increment
  have hnorm : Tendsto (fun ε=>Complex.normSq (E ε)) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,he0,Complex.normSq_I] using
      (Complex.continuous_normSq.tendsto (E 0)).comp
        (hE.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hn := hnorm.div_const 2
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε≠0 := ne_of_gt hε
  have hnorm : Complex.normSq (circle ε-1)=2*(1-Real.cos ε) := by
    have hre : (circle ε).re=Real.cos ε := by
      simp [circle]
    have him : (circle ε).im=Real.sin ε := by
      simp [circle]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero,hre,him]
    nlinarith [Real.sin_sq_add_cos_sq ε]
  have hh := congrArg Complex.normSq (he ε)
  rw [hnorm,Complex.normSq_mul,Complex.normSq_ofReal] at hh
  field_simp [hε0]
  nlinarith

theorem linear_coeff_ratio_limit {P : ℝ→Polynomial ℝ} {N : ℕ}
    (hdeg : ∀ ε,(P ε).natDegree<N+2)
    (hc : ∀ j,Tendsto (fun ε=>(P ε).coeff j) (𝓝[>] (0:ℝ)) (𝓝 ((P 0).coeff j)))
    {L₀ L₁ : ℝ}
    (h₀ : Tendsto (fun ε : ℝ=>(P ε).coeff 0/ε^3) (𝓝[>] (0:ℝ)) (𝓝 L₀))
    (h₁ : Tendsto (fun ε : ℝ=>(P ε).eval (1-Real.cos ε)/ε^3) (𝓝[>] (0:ℝ)) (𝓝 L₁)) :
    Tendsto (fun ε : ℝ=>(P ε).coeff 1/ε) (𝓝[>] (0:ℝ)) (𝓝 (2*(L₁-L₀))) := by
  let x (ε : ℝ) := 1-Real.cos ε
  let R (ε : ℝ) := x ε/ε^2
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hx : Tendsto x (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hcos := Real.continuous_cos.continuousAt.tendsto.comp he
    have h1 : Tendsto (fun _ : ℝ=>(1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa only [Real.cos_zero,sub_self,Function.comp_def] using h1.sub hcos
  have hR : Tendsto R (𝓝[>] (0:ℝ)) (𝓝 (1/2:ℝ)) := one_sub_cos_ratio_limit
  have htail : Tendsto (fun ε=>tailEval (P ε) N (x ε)) (𝓝[>] (0:ℝ))
      (𝓝 (tailEval (P 0) N 0)) := by
    unfold tailEval
    exact tendsto_finsetSum _ (fun j _=>(hc (j+2)).mul (hx.pow j))
  have herr : Tendsto (fun ε=>ε*(R ε)^2*tailEval (P ε) N (x ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (he.mul (hR.pow 2)).mul htail
  have hmain := ((h₁.sub h₀).sub herr).div hR (by norm_num : (1/2:ℝ)≠0)
  have hEq : (fun ε : ℝ=>((P ε).eval (1-Real.cos ε)/ε^3-(P ε).coeff 0/ε^3-
      ε*(R ε)^2*tailEval (P ε) N (x ε))/R ε)=ᶠ[𝓝[>] (0:ℝ)]
      (fun ε=>(P ε).coeff 1/ε) := by
    have hnR : ∀ᶠ ε in 𝓝[>] (0:ℝ),R ε≠0 := hR.eventually (isOpen_compl_singleton.mem_nhds (by norm_num : (1/2:ℝ)≠0))
    filter_upwards [hnR,self_mem_nhdsWithin] with ε hnR hε
    have he0 : ε≠0 := ne_of_gt hε
    have hx0 : x ε≠0 := by intro hh;apply hnR;simp [R,hh]
    change ((P ε).eval (x ε)/ε^3-(P ε).coeff 0/ε^3-
      ε*(R ε)^2*tailEval (P ε) N (x ε))/R ε=(P ε).coeff 1/ε
    rw [eval_split_tail (P ε) (hdeg ε)]
    dsimp [R]
    field_simp [he0,hx0]
    ring
  convert! hmain.congr' hEq using 1
  congr 1
  ring

theorem coefficient_zero_of_ratio {f : ℝ→ℝ} {k : ℕ} (hk : 0<k) {L : ℝ}
    (hc : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)))
    (hlim : Tendsto (fun ε : ℝ=>f ε/ε^k) (𝓝[>] (0:ℝ)) (𝓝 L)) : f 0=0 := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun ε : ℝ=>(f ε/ε^k)*ε^k) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_pow hk.ne',mul_zero] using hlim.mul (he.pow k)
  have hEq : (fun ε : ℝ=>(f ε/ε^k)*ε^k)=ᶠ[𝓝[>] (0:ℝ)] f := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_mul_cancel₀ _ (pow_ne_zero k (ne_of_gt hε))
  exact tendsto_nhds_unique hc (hh.congr' hEq)

end
end nesterov.Faithful
