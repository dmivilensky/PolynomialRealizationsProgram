import polyak.Boundary.P5.LagExpr
import polyak.Boundary.P5.Active
import polyak.Numerics.Parametric.Weighted

/-! A finite signed-prefix checker for the original P5 primal slacks.
The four active equations come from the source system; every other constraint
is checked on the actual parameter box, after exact division at h=0. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def lagSign (positive : Bool) : ℚ := if positive then 1 else -1

def criticalLag (n : ℕ) (positive : Bool) : Bool :=
  decide (n%3=0 ∨ (n%3=1 ∧ positive=false) ∨ (n%3=2 ∧ positive=true))

def activeLag (n : ℕ) (positive : Bool) : Bool :=
  decide ((n=1 ∧ positive=false) ∨ (positive=true ∧ (n=2 ∨ n=3 ∨ n=5)))

def prefixExpr (n : ℕ) (code : LagCode n) (positive : Bool) : Expr :=
  if criticalLag n positive then dividedSlackExpr n code (lagSign positive)
  else .add (.const (3/2)) (.mul (.var 0) (dividedSlackExpr n code (lagSign positive)))

def lagCheck (n : ℕ) (code : LagCode n) (positive : Bool)
    (I : IntervalRat) (X : Fin 7 → IntervalRat) (cfg : DyadicConfig) : Bool :=
  if activeLag n positive then true
  else boundCheck (prefixExpr n code positive) I X cfg true

def prefixCheck (codes : (n : Fin 24) → LagCode n)
    (I : IntervalRat) (cert : WeightedCertificate 7) (cfg : DyadicConfig) : Bool :=
  decide (∀ (n : Fin 24) (positive : Bool), 1≤(n : ℕ) →
    lagCheck n (codes n) positive I (coordinateBox cert.center cert.radius) cfg=true)

noncomputable section

theorem lagSign_sign (positive : Bool) :
    (lagSign positive : ℝ)= -1 ∨ (lagSign positive : ℝ)=1 := by
  cases positive <;> norm_num [lagSign]

theorem criticalLag_iff (n : ℕ) (positive : Bool) :
    criticalLag n positive=true ↔ CriticalPair n (lagSign positive) := by
  cases positive <;> norm_num [criticalLag,CriticalPair,lagSign]

theorem activeLag_iff (n : ℕ) (positive : Bool) :
    activeLag n positive=true ↔ ActivePair n (lagSign positive) := by
  cases positive <;> norm_num [activeLag,ActivePair,lagSign]

theorem actualPrimal_eq_raw_div {h : ℝ} (hh : 0≤h) (Z : Coordinates)
    {n : ℕ} (hn : 1≤n) (σ : ℝ) :
    actualPrimal h Z n σ=rawBranch h Z n σ/lagDenominator (1+h) n := by
  have hd := (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) n hn).ne'
  unfold actualPrimal rawBranch
  field_simp [hd]

theorem lagCheck_sound {n : ℕ} (hn : 1≤n) (code : LagCode n) (positive : Bool)
    (I : IntervalRat) (X : Fin 7 → IntervalRat) (cfg : DyadicConfig)
    (hc : lagCheck n code positive I X cfg=true)
    {h : ℝ} {Z : Coordinates} (hh : 0≤h) (hs : h∈I) (hX : FinBoxMem Z X)
    (hZ : regularSystem (h,Z)=0) : 0≤actualPrimal h Z n (lagSign positive) := by
  by_cases ha : activeLag n positive=true
  · have ha' := (activeLag_iff n positive).mp ha
    obtain ⟨h1,h2,h3,h5⟩ := active_slacks_zero hh hZ
    rcases ha' with ⟨rfl,hs⟩ | ⟨rfl,hs⟩ | ⟨rfl,hs⟩ | ⟨rfl,hs⟩
    · rw [hs]; exact h1.ge
    · rw [hs]; exact h2.ge
    · rw [hs]; exact h3.ge
    · rw [hs]; exact h5.ge
  · simp only [lagCheck,ha] at hc
    have hp := boundCheck_sound (prefixExpr n code positive) I X cfg true hc hs hX
    change 0<eval (prefixExpr n code positive) h Z at hp
    rw [actualPrimal_eq_raw_div hh Z hn]
    apply div_nonneg _ (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) n hn).le
    rw [rawBranch_division n code]
    by_cases hk : criticalLag n positive=true
    · have he := critical_actualRaw_zero hn ((criticalLag_iff n positive).mp hk)
      rw [he,zero_add]
      simp only [prefixExpr,hk,↓reduceIte,dividedSlackExpr_eval] at hp
      exact mul_nonneg hh hp.le
    · have he := noncritical_actualRaw_eq hn (lagSign_sign positive)
        (fun hf => hk ((criticalLag_iff n positive).mpr hf))
      rw [he]
      have hk' : criticalLag n positive=false := Bool.eq_false_iff.mpr hk
      simp only [prefixExpr,hk',Bool.false_eq_true,↓reduceIte] at hp
      change 0<((3/2 : ℚ) : ℝ)+h*eval (dividedSlackExpr n code (lagSign positive)) h Z at hp
      rw [dividedSlackExpr_eval] at hp
      norm_num only [Rat.cast_div,Rat.cast_ofNat] at hp
      exact hp.le

theorem prefixCheck_sound (codes : (n : Fin 24) → LagCode n)
    (I : IntervalRat) (cert : WeightedCertificate 7) (cfg : DyadicConfig)
    (hc : prefixCheck codes I cert cfg=true)
    {h : ℝ} {Z : Coordinates} (hh : 0≤h) (hs : h∈I)
    (hX : FinBoxMem Z (coordinateBox cert.center cert.radius))
    (hZ : regularSystem (h,Z)=0) :
    ∀ n : ℕ, 1≤n → n<24 → ∀ σ : ℝ, (σ= -1 ∨ σ=1) → 0≤actualPrimal h Z n σ := by
  simp only [prefixCheck,decide_eq_true_eq] at hc
  intro n hn hn24 σ hσ
  rcases hσ with rfl | rfl
  · simpa [lagSign] using lagCheck_sound hn (codes ⟨n,hn24⟩) false I _ cfg
      (hc ⟨n,hn24⟩ false hn) hh hs hX hZ
  · simpa [lagSign] using lagCheck_sound hn (codes ⟨n,hn24⟩) true I _ cfg
      (hc ⟨n,hn24⟩ true hn) hh hs hX hZ

end
end polyak.Boundary.P5
