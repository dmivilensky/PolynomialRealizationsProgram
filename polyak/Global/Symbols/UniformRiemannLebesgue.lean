import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Uniform Riemann-Lebesgue decay on every compact family in genuine L¹.
The proof uses a finite L¹-net and the norm-one Fourier integral bound. -/
noncomputable section
namespace polyak.Global.Symbols
open MeasureTheory Filter Set Topology
open scoped FourierTransform

abbrev RealL1 := Lp ℂ 1 (volume : Measure ℝ)

def fourierL1 (f : RealL1) (ξ : ℝ) : ℂ := 𝓕 (f : ℝ→ℂ) ξ

theorem fourierL1_norm_sub_le (f g : RealL1) (ξ : ℝ) :
    ‖fourierL1 f ξ-fourierL1 g ξ‖≤‖f-g‖ := by
  have hf : Integrable (fun x : ℝ=>𝐞 (-inner ℝ x ξ) • f x) :=
    (Real.fourierIntegral_convergent_iff (E := ℂ) (μ := volume) ξ).mpr
      (L1.integrable_coeFn f)
  have hg : Integrable (fun x : ℝ=>𝐞 (-inner ℝ x ξ) • g x) :=
    (Real.fourierIntegral_convergent_iff (E := ℂ) (μ := volume) ξ).mpr
      (L1.integrable_coeFn g)
  unfold fourierL1
  rw [Real.fourier_eq,Real.fourier_eq,←integral_sub hf hg]
  calc
    _≤∫x : ℝ,‖𝐞 (-inner ℝ x ξ) • f x-𝐞 (-inner ℝ x ξ) • g x‖ :=
      norm_integral_le_integral_norm _
    _=∫x : ℝ,‖f x-g x‖ := by simp only [←smul_sub,Circle.norm_smul]
    _=‖f-g‖ := by
      change (∫x : ℝ,‖((f : ℝ→ℂ)-(g : ℝ→ℂ)) x‖)=‖f-g‖
      rw [integral_norm_eq_lintegral_enorm ((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g)),
        L1.norm_sub_eq_lintegral]
      rfl

theorem compact_uniform_decay {X : Type*} [PseudoMetricSpace X] {ι : Type*}
    (F : ι→X→ℂ) {l : Filter ι} {K : Set X} (hK : IsCompact K)
    (hLip : ∀i x y,‖F i x-F i y‖≤dist x y)
    (hpoint : ∀x,Tendsto (fun i=>F i x) l (𝓝 0)) :
    TendstoUniformlyOn F (fun _=>0) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨T,hT,hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε/2) (by linarith)
  have hfinite : ∀ᶠi in l,∀x∈T,‖F i x‖<ε/2 := by
    apply hT.eventually_all.mpr
    intro x _
    exact (tendsto_zero_iff_norm_tendsto_zero.mp (hpoint x)).eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))
  filter_upwards [hfinite] with i hi
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hdist : dist x y<ε/2 := hxy
  simp only [dist_zero_left]
  calc
    ‖F i x‖≤‖F i x-F i y‖+‖F i y‖ := norm_le_norm_sub_add _ _
    _≤dist x y+‖F i y‖ := add_le_add (hLip i x y) le_rfl
    _<ε := by linarith [hi y hy]

theorem uniform_RiemannLebesgue {K : Set RealL1} (hK : IsCompact K) :
    TendstoUniformlyOn (fun ξ f=>fourierL1 f ξ) (fun _=>0) (cocompact ℝ) K := by
  apply compact_uniform_decay _ hK
  · intro ξ f g
    simpa only [dist_eq_norm] using fourierL1_norm_sub_le f g ξ
  · intro f
    exact Real.zero_at_infty_fourier (f : ℝ→ℂ)

end polyak.Global.Symbols
