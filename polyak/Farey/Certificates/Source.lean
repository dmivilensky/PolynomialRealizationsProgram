import polyak.Farey.Certificates.Fan
import polyak.Levels.Program.SourceIdentities

/-! Literal source slacks and the strict t=0 certificate represented by a
finite signed family. The density is retained, including both endpoints. -/
noncomputable section
namespace polyak.Farey.Certificates
open Levels Set
open scoped BigOperators
variable {I:Type*} [Fintype I]

def rawIndexedSymbol (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) (γ:ℝ) (ω:Frequency) : ℝ:=
  (∑i,a i*sourceLag q (n i) ω)+γ*sourceG q ω

theorem rawIndexedSymbol_factor (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) (γ:ℝ) (ω:Frequency) :
    rawIndexedSymbol q n a γ ω=sourceDensity q ω*
      ((∑i,a i*(tuningCurve q).lag (n i) ω)+γ*(tuningCurve q).minimizer ω) := by
  unfold rawIndexedSymbol
  simp_rw [sourceLag_polar,sourceG_polar]
  rw [mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

theorem rawIndexedSymbol_continuous (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) (γ:ℝ) :
    Continuous (rawIndexedSymbol q n a γ) := by
  unfold rawIndexedSymbol
  fun_prop

theorem raw_polynomial_strict (q:General.Tuning) (n:I→ℤ) (a:I→ℝ) {γ:ℝ}
    (hn:∀i,n i≠0) (ha:∀i,0≤a i) (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,indexedPolynomial q n a γ c<0) :
    ∃ε:ℝ,0<ε ∧ ∀ω:Frequency,rawIndexedSymbol q n a γ ω≤-ε := by
  have hneg (ω:Frequency) : rawIndexedSymbol q n a γ ω<0 := by
    rw [rawIndexedSymbol_factor]
    exact mul_neg_of_pos_of_neg (sourceDensity_pos q ω)
      (indexed_polynomial_negative q n a hn ha hγ hP ω)
  obtain ⟨ω,_,hmax⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (rawIndexedSymbol_continuous q n a γ).continuousOn
  refine ⟨-rawIndexedSymbol q n a γ ω,neg_pos.mpr (hneg ω),?_⟩
  intro x
  simpa only [neg_neg] using (show rawIndexedSymbol q n a γ x≤rawIndexedSymbol q n a γ ω
    from hmax (mem_univ x))

/-- Gamma/2 on each minimizer constraint cancels the common value constant
exactly at t=0, for every choice of the lower and upper lag coefficients. -/
theorem zero_shift_common_value_cancel (F:Finset ℕ) (α β:ℕ→ℝ) (γ:ℝ) :
    (∑n∈F,(α n-β n)*Real.sinh ((n:ℝ)*0))+γ/2-γ/2=0 := by simp

theorem familyLag_mem_fanLags (K:ℕ) (P N:Finset ℕ) (hN:∀m∈N,0<m)
    (i:Sum {m//m∈P} {m//m∈N}) : familyLag K i∈fanLags K := by
  cases i with
  | inl m => exact Or.inl ⟨m.val,rfl⟩
  | inr m => exact Or.inr ⟨m.val,hN _ m.property,rfl⟩

theorem fan_formula_source_strict (q:General.Tuning) {K:ℕ} (hK:2≤K) (P N:Finset ℕ)
    (hN:∀m∈N,0<m) (a b:ℕ→ℝ) (ha:∀m∈P,0≤a m) (hb:∀m∈N,0≤b m)
    {γ:ℝ} (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,fanLeft q K P N a b γ c<fanRight K P N a b c) :
    ∃ε:ℝ,0<ε ∧ ∀ω:Frequency,
      rawIndexedSymbol q (familyLag K (P:=P) (N:=N)) (familyWeight a b) γ ω≤-ε := by
  apply raw_polynomial_strict
  · intro i
    cases i with
    | inl m => change ((m.val*K+1:ℕ):ℤ)≠0; omega
    | inr m =>
      change -((m.val*K:ℕ):ℤ)≠0
      have hp:=Nat.mul_pos (hN _ m.property) (by omega : 0<K)
      omega
  · intro i
    cases i with
    | inl m => exact ha _ m.property
    | inr m => exact hb _ m.property
  · exact hγ
  · intro c hc
    rw [fan_polynomial_identity q (by omega) P N hN]
    exact sub_neg.mpr (hP c hc)

end polyak.Farey.Certificates
