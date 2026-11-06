import nesterov.Layer.NegativeBandGeometry
import nesterov.Layer.SymbolLimits

/-! Uniform symbol signs and mixed-symbol bounds on one rational layer band. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

theorem layer_negative_band_symbols {B c s₁ : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hc : max (Layer.Lambda θ y B) 0/3<c) (hs₁ : 0<s₁) :
    ∃ s a b D M : ℝ,s∈Ioc (0:ℝ) (min s₁ (1/6)) ∧ 0<a ∧ a<b ∧ 0<D ∧ 0<M ∧
      a<(1-s)^2*(B*y/(2-y)) ∧ (1+s)^2*(B*y/(2-y))<b ∧
      ∀ᶠ p in l, ∀ ω∈Spread.band s (2*Real.pi/F.layerPeriod B p),
        (1-Real.cos ω)/Real.sqrt (F.epsilon p)∈Icc a b ∧
        |mixedPolynomial (F.tuning p).beta (F.tuning p).tau
          ((F.tuning p).stepSize*F.epsilon p^2) (F.tuning p).stepSize
          (1-c*F.epsilon p) (1-Real.cos ω)|≤M*F.epsilon p ∧
        ((1-circle (1-c*F.epsilon p) ω)*Spread.product (F.tuning p) (F.epsilon p^2) 1
          (1-c*F.epsilon p) ω).re≤ -D*F.epsilon p*Real.sqrt (F.epsilon p) := by
  let φ : ℝ := B*y/(2-y)
  let P : ℝ→ℝ := fun x=>x*Layer.polynomial θ y c B x
  have hφ : 0<φ := div_pos (mul_pos hBp F.step_pos) (by linarith)
  have hP : Continuous P := by dsimp [P,Layer.polynomial];fun_prop
  have hneg : P φ<0 := mul_neg_of_pos_of_neg hφ
    (Layer.polynomial_min_neg F.step_pos hy2 hBp hc)
  obtain ⟨s,a,b,m,hs,ha,hab,hm,hlo,hhi,hPneg⟩ := Layer.negative_interval hP hφ hneg hs₁
  have hs6 : s∈Ioc (0:ℝ) (1/6) := ⟨hs.1,hs.2.trans (min_le_right _ _)⟩
  have hgeometry := F.layer_band_geometry hy2 hBp hs6 hlo hhi
  obtain ⟨M,hM,hmixed⟩ := F.layer_mixed_bounded c hB (isCompact_Icc (a:=a) (b:=b))
  have hH := Metric.tendstoUniformlyOn_iff.mp
    (F.layer_cubic_uniform c hB (isCompact_Icc (a:=a) (b:=b))) (m/2) (by positivity)
  refine ⟨s,a,b,m/2,M,hs,ha,hab,by positivity,hM,hlo,hhi,?_⟩
  filter_upwards [hgeometry.1,hmixed,hH,F.epsilon_pos,F.layerCubic_actual c,F.layerMixed_actual c]
    with p hgeo hmix hH he hActual hMixed ω hω
  have hφmem := hgeo.2 ω hω
  let x : ℝ := (1-Real.cos ω)/Real.sqrt (F.epsilon p)
  have hx : x∈Icc a b := hφmem
  have hscale : Real.sqrt (F.epsilon p)*x=1-Real.cos ω := by
    dsimp [x]
    field_simp [(Real.sqrt_pos.mpr he).ne']
  refine ⟨hφmem,?_,?_⟩
  · have hh := hmix x hx
    rw [hscale] at hh
    rw [hMixed]
    exact hh
  · have hh := hH x hx
    have hdist : |F.layerCubic c p (Real.sqrt (F.epsilon p)*x)/
        (F.epsilon p*Real.sqrt (F.epsilon p))-P x|<m/2 := by
      simpa only [Real.dist_eq,abs_sub_comm,P] using hh
    have hupper : F.layerCubic c p (Real.sqrt (F.epsilon p)*x)/
        (F.epsilon p*Real.sqrt (F.epsilon p))≤ -(m/2) := by
      have hp := hPneg x hx
      have hd := (abs_lt.mp hdist).2
      linarith
    rw [hscale,←hActual] at hupper
    have hfinal := (div_le_iff₀ (mul_pos he (Real.sqrt_pos.mpr he))).mp hupper
    nlinarith only [hfinal]

end
end nesterov.TwoStep.Scaling
