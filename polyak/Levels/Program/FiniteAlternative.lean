import polyak.Levels.Program.Normalization
import polyak.Duality.FiniteAlternative

/-! Strict finite-dimensional separation on the full compact space of measures. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Pointwise
namespace polyak.Levels

def angleMomentImage {I : Type*} (φ : I → C(Frequency,ℝ)) : Set (I → ℝ) :=
  Set.range (fun ν : ProbabilityMeasure Frequency => fun i => ∫ ω, φ i ω ∂ν)

theorem isCompact_angleMomentImage {I : Type*} [Fintype I] (φ : I → C(Frequency,ℝ)) :
    IsCompact (angleMomentImage φ) :=
  isCompact_range (continuous_pi fun i => ProbabilityMeasure.continuous_integral_continuousMap (φ i))

def mixAngleMeasure (μ ν : ProbabilityMeasure Frequency) (u v : ℝ)
    (hu : 0≤u) (hv : 0≤v) (huv : u+v=1) : ProbabilityMeasure Frequency :=
  ⟨ENNReal.ofReal u • (μ:Measure Frequency)+ENNReal.ofReal v • (ν:Measure Frequency),
    ⟨by simp [Measure.add_apply,Measure.smul_apply,← ENNReal.ofReal_add hu hv,huv]⟩⟩

theorem integral_mixAngleMeasure (μ ν : ProbabilityMeasure Frequency) (u v : ℝ)
    (hu : 0≤u) (hv : 0≤v) (huv : u+v=1) (f : C(Frequency,ℝ)) :
    (∫ ω, f ω ∂mixAngleMeasure μ ν u v hu hv huv)=
      u*(∫ ω, f ω ∂μ)+v*(∫ ω, f ω ∂ν) := by
  change (∫ ω, f ω ∂(ENNReal.ofReal u • (μ:Measure Frequency)+
    ENNReal.ofReal v • (ν:Measure Frequency)))=_
  rw [integral_add_measure]
  · simp [integral_smul_measure,ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hv]
  · exact (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).smul_measure ENNReal.ofReal_ne_top
  · exact (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).smul_measure ENNReal.ofReal_ne_top

theorem convex_angleMomentImage {I : Type*} (φ : I → C(Frequency,ℝ)) :
    Convex ℝ (angleMomentImage φ) := by
  rintro x ⟨μ,rfl⟩ y ⟨ν,rfl⟩ u v hu hv huv
  refine ⟨mixAngleMeasure μ ν u v hu hv huv,?_⟩
  funext i
  exact integral_mixAngleMeasure μ ν u v hu hv huv (φ i)

theorem finite_measure_alternative {I : Type*} [Fintype I] (φ : I → C(Frequency,ℝ))
    (hinfeasible : ¬ ∃ ν : ProbabilityMeasure Frequency, ∀ i,0≤∫ ω,φ i ω ∂ν) :
    ∃ (w : I→ℝ) (ε:ℝ), (∀ i,0≤w i) ∧ 0<ε ∧ ∀ ω,(∑ i,w i*φ i ω)≤-ε := by
  classical
  let Q : Set (I→ℝ) := {x | ∀ i,0≤x i}
  have hclosed : IsClosed Q := by
    simp only [Q,Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hconvex : Convex ℝ Q := by
    intro x hx y hy a b ha hb _ i
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have hdisj : Disjoint (angleMomentImage φ) Q := by
    rw [Set.disjoint_left]
    rintro x ⟨ν,rfl⟩ hx
    exact hinfeasible ⟨ν,hx⟩
  obtain ⟨f,u,v,hleft,huv,hright⟩ := geometric_hahn_banach_compact_closed
    (convex_angleMomentImage φ) (isCompact_angleMomentImage φ) hconvex hclosed hdisj
  have hv : v≤0 := by simpa using (hright 0 (fun _ => le_rfl)).le
  have hnonneg (x : I→ℝ) (hx : ∀ i,0≤x i) : 0≤f x := by
    by_contra hn
    have hfx : f x<0 := lt_of_not_ge hn
    obtain ⟨r,hr,hrv⟩ := exists_pos_lt_mul (neg_pos.mpr hfx) (-v)
    have hs := hright (r•x) (fun i => mul_nonneg hr.le (hx i))
    simp only [map_smul,smul_eq_mul] at hs
    nlinarith
  let w : I→ℝ := fun i => f (Pi.single i 1)
  have hrepr (x : I→ℝ) : f x=∑ i,w i*x i := by
    have hx : x=∑ i,x i•Pi.single i (1:ℝ) := by ext j; simp [Pi.single_apply,mul_ite]
    conv_lhs => rw [hx]
    simp only [map_sum,map_smul,smul_eq_mul,w]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨w,-u,?_,by linarith,?_⟩
  · intro i
    exact hnonneg _ (fun j => by simp [Pi.single_apply]; split_ifs <;> positivity)
  · intro ω
    let ν : ProbabilityMeasure Frequency := ⟨Measure.dirac ω,inferInstance⟩
    have hd := hleft (fun i => ∫ η,φ i η ∂ν) ⟨ν,rfl⟩
    have heq : (fun i => ∫ η,φ i η ∂ν)=fun i => φ i ω := by
      funext i
      exact integral_dirac (φ i) ω
    rw [heq,hrepr] at hd
    simpa using hd.le

end polyak.Levels
