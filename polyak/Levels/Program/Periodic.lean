import polyak.Levels.Program.Pinning
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Article: exact finite lag reduction on the actual periodic grid. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

def PeriodicSolution (Θ : Curve) (k : ℕ) (w : Measure Frequency) : Prop :=
  IsFiniteMeasure w ∧ w≠0 ∧ (∀ᵐω ∂w,ω∈periodicGrid k) ∧
    0≤∫ω,Θ.minimizer ω ∂w ∧ ∀n : ℕ,0<n→n<k→0≤∫ω,Θ.lag (n:ℤ) ω ∂w

theorem periodicSolution_iff {Θ : Curve} {k : ℕ} (hk : 0<k) (w : Measure Frequency) :
    PeriodicSolution Θ k w ↔
      ProgramSolution Θ nonzeroLags w ∧ ∀ᵐω ∂w,ω∈periodicGrid k := by
  constructor
  · rintro ⟨hf,hn,hgrid,hmin,hl⟩
    refine ⟨⟨hf,hn,hmin,fun n _=>?_⟩,hgrid⟩
    have hrem : 0≤n%(k:ℤ) ∧ n%(k:ℤ)<k :=
      ⟨Int.emod_nonneg n (by omega),Int.emod_lt_of_pos n (by omega)⟩
    have he : (∫ω,Θ.lag n ω ∂w)=∫ω,Θ.lag (n%(k:ℤ)) ω ∂w := by
      apply integral_congr_ae
      filter_upwards [hgrid] with ω hω
      exact lag_mod_grid Θ hω n
    rw [he]
    by_cases hz : n%(k:ℤ)=0
    · simp [hz,Curve.lag_zero]
    · have hcast : ((n%(k:ℤ)).toNat:ℤ)=n%(k:ℤ):=Int.toNat_of_nonneg hrem.1
      rw [←hcast]
      exact hl _ (by omega) (by omega)
  · rintro ⟨⟨hf,hn,hmin,hl⟩,hgrid⟩
    exact ⟨hf,hn,hgrid,hmin,fun n hn _=>hl n (by change (n:ℤ)≠0; omega)⟩

theorem periodicFP_iff_finite (Θ : Curve) {k : ℕ} (hk : 0<k) :
    PeriodicFP Θ k ↔ ∃w : Measure Frequency,PeriodicSolution Θ k w := by
  simp only [PeriodicFP,←periodicSolution_iff hk]

end polyak.Levels
