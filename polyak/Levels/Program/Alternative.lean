import polyak.Levels.Program.FiniteAlternative
import Mathlib.Algebra.BigOperators.Option

/-! Exact alternative for every subset of the signed integer lags. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace polyak.Levels

theorem exists_finite_infeasible (Θ : Curve) (𝒩 : Set ℤ) (h : ¬FPOn Θ 𝒩) :
    ∃ F : Finset ℤ, (F:Set ℤ) ⊆ 𝒩 ∧ ¬FPOn Θ (F:Set ℤ) := by
  classical
  by_contra hnone
  push Not at hnone
  let P : Set (ProbabilityMeasure Frequency) := {ν | 0≤∫ ω,Θ.minimizer ω ∂ν}
  let T : 𝒩 → Set (ProbabilityMeasure Frequency) := fun n =>
    {ν | 0≤∫ ω,Θ.lag n ω ∂ν}
  have hPc : IsCompact P := IsClosed.isCompact (isClosed_le continuous_const
    (ProbabilityMeasure.continuous_integral_continuousMap
      (show C(Frequency,ℝ) from ⟨Θ.minimizer,Θ.continuous_minimizer⟩)))
  have hTc (n:𝒩) : IsClosed (T n) := isClosed_le continuous_const
    (ProbabilityMeasure.continuous_integral_continuousMap
      (show C(Frequency,ℝ) from ⟨Θ.lag n,Θ.continuous_lag n⟩))
  have hfinite (s : Finset 𝒩) : (P ∩ ⋂ n∈s,T n).Nonempty := by
    let F : Finset ℤ := s.image Subtype.val
    have hsub : (F:Set ℤ) ⊆ 𝒩 := by
      intro n hn
      obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hn
      exact m.property
    obtain ⟨ν,hν⟩ := (fpOn_iff_probability Θ (F:Set ℤ)).mp (hnone F hsub)
    refine ⟨ν,hν.1,?_⟩
    apply Set.mem_iInter.mpr
    intro n
    apply Set.mem_iInter.mpr
    intro hn
    exact hν.2 n (Finset.mem_image.mpr ⟨n,hn,rfl⟩)
  obtain ⟨ν,hν⟩ := hPc.inter_iInter_nonempty T hTc hfinite
  apply h
  apply (fpOn_iff_probability Θ 𝒩).mpr
  refine ⟨ν,hν.1,fun n hn => ?_⟩
  exact Set.mem_iInter.mp hν.2 ⟨n,hn⟩

def finiteConstraintMap (Θ : Curve) (F : Finset ℤ) : Option {n // n∈F} → C(Frequency,ℝ)
  | none => ⟨Θ.minimizer,Θ.continuous_minimizer⟩
  | some n => ⟨Θ.lag n,Θ.continuous_lag n⟩

theorem strictSymbol_of_finite_infeasible (Θ : Curve) (𝒩 : Set ℤ) (F : Finset ℤ)
    (hsub : (F:Set ℤ) ⊆ 𝒩) (h : ¬FPOn Θ (F:Set ℤ)) : Nonempty (StrictSymbol Θ 𝒩) := by
  classical
  have hi : ¬ ∃ν : ProbabilityMeasure Frequency,
      ∀i,0≤∫ ω,finiteConstraintMap Θ F i ω ∂ν := by
    rintro ⟨ν,hν⟩
    apply h
    apply (fpOn_iff_probability Θ (F:Set ℤ)).mpr
    exact ⟨ν,hν none,fun n hn => hν (some ⟨n,hn⟩)⟩
  obtain ⟨w,ε,hw,hε,hs⟩ := finite_measure_alternative (finiteConstraintMap Θ F) hi
  let a : ℤ→ℝ := fun n => if hn:n∈F then w (some ⟨n,hn⟩) else 0
  let S : CertificateSymbol Θ 𝒩 := {
    lags := F
    lags_subset := fun n hn => hsub hn
    weight := a
    weight_nonneg := fun n hn => by simp only [a,hn,↓reduceDIte]; exact hw _
    gamma := w none
    gamma_nonneg := hw _ }
  refine ⟨S,ε,hε,?_⟩
  intro ω
  have he := hs ω
  rw [Fintype.sum_option] at he
  change (∑n∈F,a n*Θ.lag n ω)+w none*Θ.minimizer ω≤-ε
  have ha (n : {n // n∈F}) : a n=w (some n) := by simp [a,n.property]
  rw [← Finset.sum_coe_sort F]
  simp only [ha]
  simpa only [finiteConstraintMap,ContinuousMap.coe_mk,add_comm] using he

theorem StrictSymbol.not_probability {Θ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩)
    (ν : ProbabilityMeasure Frequency) : ¬ProbabilitySolution Θ 𝒩 ν := by
  intro hν
  have hi (n:ℤ) : Integrable (fun ω => S.symbol.weight n*Θ.lag n ω) (ν:Measure Frequency) :=
    (integrable_curve_lag Θ n ν).const_mul _
  have hsum := integrable_finsetSum S.symbol.lags (fun n _ => hi n)
  have hmin := (integrable_curve_minimizer Θ ν).const_mul S.symbol.gamma
  have hnonneg : 0≤∫ ω,S.symbol.eval ω ∂ν := by
    unfold CertificateSymbol.eval
    rw [integral_add hsum hmin,integral_finsetSum _ (fun n _ => hi n),integral_const_mul]
    simp only [integral_const_mul]
    exact add_nonneg (Finset.sum_nonneg (fun n hn =>
      mul_nonneg (S.symbol.weight_nonneg n hn) (hν.2 n (S.symbol.lags_subset n hn))))
      (mul_nonneg S.symbol.gamma_nonneg hν.1)
  have hneg := integral_mono (hsum.add hmin) (integrable_const (-S.epsilon)) S.strict
  change (∫ ω,S.symbol.eval ω ∂(ν:Measure Frequency))≤
    (∫ _ : Frequency,(-S.epsilon:ℝ) ∂(ν:Measure Frequency)) at hneg
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hneg
  linarith [S.epsilon_pos]

theorem StrictSymbol.not_fpOn {Θ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩) : ¬FPOn Θ 𝒩 := by
  intro h
  obtain ⟨ν,hν⟩ := (fpOn_iff_probability Θ 𝒩).mp h
  exact S.not_probability ν hν

theorem infeasible_iff_strictSymbol (Θ : Curve) (𝒩 : Set ℤ) :
    (¬FPOn Θ 𝒩) ↔ Nonempty (StrictSymbol Θ 𝒩) := by
  constructor
  · intro h
    obtain ⟨F,hsub,hF⟩ := exists_finite_infeasible Θ 𝒩 h
    exact strictSymbol_of_finite_infeasible Θ 𝒩 F hsub hF
  · rintro ⟨S⟩
    exact S.not_fpOn

end polyak.Levels
