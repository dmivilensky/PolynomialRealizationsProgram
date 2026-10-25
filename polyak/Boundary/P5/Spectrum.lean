import polyak.Boundary.P5.LocalLimits
import polyak.Waves.Finite

/-!
Article: the actual two-atom spectrum of the central P5 branch.
Use: exact probability normalization, moments, and signed lag identities.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral MeasureTheory
open scoped NNReal ENNReal

/-- Article: the two nonnegative probability weights, with main atom first. -/
def twoAtomWeights (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : Bool → ℝ≥0 :=
  fun b => if b then ⟨p,hp⟩ else ⟨1-p,sub_nonneg.mpr hp1⟩

/-- Article: exact probability normalization of the two weights. -/
theorem twoAtomWeights_sum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    ∑ b,twoAtomWeights p hp hp1 b=1 := by
  apply Subtype.ext
  change ((∑ b,twoAtomWeights p hp hp1 b : ℝ≥0) : ℝ)=(1 : ℝ)
  simp only [Fintype.sum_bool,twoAtomWeights,Bool.false_eq_true,NNReal.coe_add]
  change p+(1-p)=1
  ring

/-- Article: the actual normalized finite spectrum, including zero auxiliary mass. -/
def twoAtomSpectrum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (x y : Frequency) : Spectrum :=
  Waves.finiteSpectrum (twoAtomWeights p hp hp1) (fun b => if b then y else x)
    (twoAtomWeights_sum p hp hp1)

/-- Article: exact averaging against the two-atom probability spectrum. -/
theorem avg_twoAtomSpectrum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (x y : Frequency)
    (f : Frequency → ℝ) : avg (twoAtomSpectrum p hp hp1 x y) f=(1-p)*f x+p*f y := by
  rw [avg,twoAtomSpectrum,Waves.finiteSpectrum_integral]
  simp only [Fintype.sum_bool,twoAtomWeights,ite_true,Bool.false_eq_true,ite_false]
  change p*f y+(1-p)*f x=(1-p)*f x+p*f y
  ring

/-- Article: at zero auxiliary mass the actual spectrum is the main Dirac measure. -/
theorem twoAtomSpectrum_zero (hp : (0 : ℝ)≤0) (hp1 : (0 : ℝ)≤1) (x y : Frequency) :
    twoAtomSpectrum 0 hp hp1 x y=⟨Measure.dirac x,by infer_instance⟩ := by
  apply Subtype.ext
  change (∑ b,((twoAtomWeights 0 hp hp1 b : ℝ≥0) : ℝ≥0∞) •
    Measure.dirac (if b then y else x))=Measure.dirac x
  have hw0 : twoAtomWeights 0 hp hp1 false=1 := by
    apply Subtype.ext
    change (1-(0 : ℝ))=1
    ring
  have hw1 : twoAtomWeights 0 hp hp1 true=0 := by apply Subtype.ext; rfl
  simp [hw0,hw1]

/-- Article: the true minimizer moment is exactly the source two-atom gap. -/
theorem meanG_twoAtomSpectrum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (x y : Frequency) (u : ℝ) :
    meanG (twoAtomSpectrum p hp hp1 x y) u=twoAtomGap u p x y := by
  rw [meanG_eq_integral,avg_twoAtomSpectrum]
  rfl

/-- Article: the true signed averaged raw slack equals its finite source numerator. -/
theorem signed_raw_twoAtomSpectrum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (x y : Frequency)
    (u t d : ℝ) (ht : t≠0) (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    meanA (twoAtomSpectrum p hp hp1 x y) u t n+
      σ*meanB (twoAtomSpectrum p hp hp1 x y) u n-
      σ*(d/Real.sinh t)*Real.sinh (n*t)=twoAtomRaw u (Real.cosh t) p d n σ x y := by
  have hsh : Real.sinh t≠0 := by simpa using ht
  have hid : d/Real.sinh t*Real.sinh (n*t)=d*lagDenominator (Real.cosh t) n := by
    rw [← lagDenominator_mul_sinh t n hn]
    field_simp [hsh]
  rw [meanA_eq_integral,meanB_eq_integral,avg_twoAtomSpectrum,avg_twoAtomSpectrum]
  unfold twoAtomRaw actualRaw lagA lagD
  rw [chebT_cosh]
  rw [show σ*(d/Real.sinh t)*Real.sinh (n*t)=σ*(d/Real.sinh t*Real.sinh (n*t)) by ring,hid]
  ring

/-- Article: exact normalization of the averaged raw slack by the positive lag denominator. -/
theorem signed_normalized_twoAtomSpectrum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (x y : Frequency)
    (u t d : ℝ) (ht : t≠0) (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    meanA (twoAtomSpectrum p hp hp1 x y) u t n+
      σ*meanB (twoAtomSpectrum p hp hp1 x y) u n-
      σ*(d/Real.sinh t)*Real.sinh (n*t)=
      lagDenominator (Real.cosh t) n*
        (((1-p)*actualRaw u (Real.cosh t) n σ x+p*actualRaw u (Real.cosh t) n σ y)/
          lagDenominator (Real.cosh t) n-σ*d) := by
  rw [signed_raw_twoAtomSpectrum p hp hp1 x y u t d ht n hn σ]
  have hd := (lagDenominator_pos (Real.one_le_cosh t) n hn).ne'
  unfold twoAtomRaw
  field_simp [hd]

/-- Article: the source positive-arcosh charge has the same magnitude for either exponent sign. -/
theorem abs_charge_cosh {h t : ℝ} (hcosh : Real.cosh t=1+h) (d : ℝ) :
    |d/Real.sinh (Real.arcosh (1+h))|=|d/Real.sinh t| := by
  by_cases ht : 0≤t
  · rw [← hcosh,Real.arcosh_cosh ht]
  · have hn : 0≤-t := by linarith
    rw [← hcosh,← Real.cosh_neg t,Real.arcosh_cosh hn,Real.sinh_neg,div_neg,abs_neg]

/-- Article: every normalized signed constraint gives genuine spectral feasibility. -/
theorem feasibleU_twoAtom_of_normalized (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (x y : Frequency)
    (u t d : ℝ) (ht : t≠0) (hstar : |d/Real.sinh t|≤twoAtomGap u p x y)
    (hprimal : ∀ n : ℕ, 1≤n → ∀ σ : ℝ, (σ= -1 ∨ σ=1) →
      0≤((1-p)*actualRaw u (Real.cosh t) n σ x+p*actualRaw u (Real.cosh t) n σ y)/
        lagDenominator (Real.cosh t) n-σ*d) :
    FeasibleU u t (twoAtomSpectrum p hp hp1 x y) (d/Real.sinh t) := by
  constructor
  · rw [meanG_twoAtomSpectrum]
    exact hstar
  · intro n hn
    have hs (σ : ℝ) (hσ : σ= -1 ∨ σ=1) :
        0≤meanA (twoAtomSpectrum p hp hp1 x y) u t n+
          σ*meanB (twoAtomSpectrum p hp hp1 x y) u n-
          σ*(d/Real.sinh t)*Real.sinh (n*t) := by
      rw [signed_normalized_twoAtomSpectrum p hp hp1 x y u t d ht n hn σ]
      exact mul_nonneg (lagDenominator_pos (Real.one_le_cosh t) n hn).le (hprimal n hn σ hσ)
    have hl := hs (-1) (Or.inl rfl)
    have hu := hs 1 (Or.inr rfl)
    constructor <;> nlinarith

end polyak.Boundary.P5
