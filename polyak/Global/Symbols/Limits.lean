import polyak.Global.Symbols.WeakConvergence
import polyak.Global.Symbols.Normalized

/-! The complete source limit lemma for arbitrary countable signed-lag
sets and uniformly convergent curves. All measure extremals are retained. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology

structure LimitSymbol (Θ : Curve) (𝒩 : Set ℤ) where
  weights : Weights 𝒩
  nonpos : ∀ω,weights.eval Θ ω≤0
  max_zero : IsGreatest (range (weights.eval Θ)) 0
  carried : ∀w : Measure Frequency,ProgramSolution Θ 𝒩 w→∀ᵐω∂w,weights.eval Θ ω=0
  support_zero : ∀w : Measure Frequency,ProgramSolution Θ 𝒩 w→w.support⊆{ω|weights.eval Θ ω=0}
  lag_slackness : ∀w : Measure Frequency,ProgramSolution Θ 𝒩 w→
    ∀n,0<weights.weight n→(∫ω,Θ.lag n ω ∂w)=0
  minimizer_slackness : ∀w : Measure Frequency,ProgramSolution Θ 𝒩 w→
    0<weights.gamma→(∫ω,Θ.minimizer ω ∂w)=0

def limitSymbolOfNonpos {Θ : Curve} {𝒩 : Set ℤ} (a : Weights 𝒩)
    (hS : ∀ω,a.eval Θ ω≤0) (hFP : FPOn Θ 𝒩) : LimitSymbol Θ 𝒩 where
  weights := a
  nonpos := hS
  max_zero := a.max_zero_of_feasible hS hFP
  carried _w hw := a.solution_carried_zero hS hw
  support_zero _w hw := a.solution_support_zero hS hw
  lag_slackness _w hw := (a.complementary_slackness hS hw).1
  minimizer_slackness _w hw := (a.complementary_slackness hS hw).2

theorem limits_of_symbols {𝒩 : Set ℤ} (a : ℕ→Weights 𝒩) (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : TendstoUniformly (fun j ω=>Θ j ω) (fun ω=>Ψ ω) atTop)
    (hS : ∀j ω,(a j).eval (Θ j) ω≤0) :
    ∃b : Weights 𝒩,∃φ : ℕ→ℕ,StrictMono φ ∧
      (∀n,Tendsto (fun j=>(a (φ j)).weight n) atTop (𝓝 (b.weight n))) ∧
      Continuous (b.eval Ψ) ∧ (∀ω,b.eval Ψ ω≤0) ∧
      (FPOn Ψ 𝒩→∃S : LimitSymbol Ψ 𝒩,S.weights=b) := by
  obtain ⟨b,φ,hφ,hc⟩ := exists_coefficient_subsequence a
  have hcurve (ω : Frequency) : Tendsto (fun j=>Θ (φ j) ω) atTop (𝓝 (Ψ ω)) :=
    (hΘ.tendsto_at ω).comp hφ.tendsto_atTop
  have hsign := limit_nonpos (fun j=>a (φ j)) b hc (fun j=>Θ (φ j)) Ψ hcurve
    (fun j=>hS (φ j))
  exact ⟨b,φ,hφ,hc,b.continuous_eval Ψ,hsign,
    fun hFP=>⟨limitSymbolOfNonpos b hsign hFP,rfl⟩⟩

theorem limits_of_normalized_finite_symbols {𝒩 : Set ℤ} (Θ : ℕ→Curve) (Ψ : Curve)
    (S : (j : ℕ)→CertificateSymbol (Θ j) 𝒩)
    (hNorm : ∀j,total (S j)=1)
    (hΘ : TendstoUniformly (fun j ω=>Θ j ω) (fun ω=>Ψ ω) atTop)
    (hS : ∀j ω,(S j).eval ω≤0) :
    ∃b : Weights 𝒩,∃φ : ℕ→ℕ,StrictMono φ ∧
      (∀n,Tendsto (fun j=>finiteCoefficient (S (φ j)) n) atTop (𝓝 (b.weight n))) ∧
      Continuous (b.eval Ψ) ∧ (∀ω,b.eval Ψ ω≤0) ∧
      (FPOn Ψ 𝒩→∃T : LimitSymbol Ψ 𝒩,T.weights=b) := by
  have hp (j : ℕ) : 0<total (S j) := by rw [hNorm j];norm_num
  obtain ⟨b,φ,hφ,hc,hcont,hsign,hmax⟩ :=
    limits_of_symbols (fun j=>normalizeWeights (S j) (hp j)) Θ Ψ hΘ
      (fun j ω=>by rw [normalizeWeights_eval,hNorm j,div_one];exact hS j ω)
  refine ⟨b,φ,hφ,?_,hcont,hsign,hmax⟩
  intro n
  simpa only [normalizeWeights,normalizedWeight_eq_finiteCoefficient _ (hNorm _) n] using hc n

theorem limit_symbol_of_infeasible_approximation {𝒩 : Set ℤ} (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : TendstoUniformly (fun j ω=>Θ j ω) (fun ω=>Ψ ω) atTop)
    (hinf : ∀j,¬FPOn (Θ j) 𝒩) (hFP : FPOn Ψ 𝒩) :
    Nonempty (LimitSymbol Ψ 𝒩) := by
  classical
  let S : (j : ℕ)→StrictSymbol (Θ j) 𝒩 := fun j=>
    Classical.choice ((infeasible_iff_strictSymbol (Θ j) 𝒩).mp (hinf j))
  obtain ⟨b,_,_,_,_,hS,_⟩ := limits_of_symbols (fun j=>normalizeStrict (S j)) Θ Ψ hΘ
    (fun j=>normalizeStrict_nonpos (S j))
  exact ⟨limitSymbolOfNonpos b hS hFP⟩

end polyak.Global.Symbols
