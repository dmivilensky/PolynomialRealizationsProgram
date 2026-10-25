import polyak.Boundary.Dual
import polyak.Duality.Certificate
import polyak.Waves.Polyak

/-!
Article: dualpoly and the G=1 minimizer correction after Lemma dualfactor.
Use: convert polynomial certificates into actual finite strict certificates of (strictcert).
Proof: exact normalized weights, their positive denominators and exact C cancellation;
equal nonnegative minimizer multipliers preserve the charge equation.
-/

noncomputable section
open scoped BigOperators
namespace polyak.Boundary
open Spectral

/-- Article: lower lag one has unit weight. -/
def lowerWeight (n : ℕ) : ℝ := if n=1 then 1 else 0

/-- Article: upper weights are divided by their proved positive normalization denominators. -/
def upperWeight (W : DualWeights) (G : ℝ) (n : ℕ) : ℝ :=
  if n ∈ W.lags then W.weight n/lagDenominator G n else 0

/-- Article: adding lower lag one does not change the supported upper weighted sum. -/
theorem sum_upperWeight (W : DualWeights) (G : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ insert 1 W.lags,upperWeight W G n*f n) =
      ∑ n ∈ W.lags,W.weight n/lagDenominator G n*f n := by
  classical
  by_cases h1 : 1 ∈ W.lags
  · rw [Finset.insert_eq_of_mem h1]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [upperWeight,ite_eq_left hn]
  · rw [Finset.sum_insert h1]
    simp only [upperWeight,ite_eq_right h1,zero_mul,zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_left hn]

/-- Article: the lower weighted sum is precisely its lag-one term. -/
theorem sum_lowerWeight (W : DualWeights) (f : ℕ → ℝ) :
    (∑ n ∈ insert 1 W.lags,lowerWeight n*f n) = f 1 := by
  classical
  rw [Finset.sum_eq_single 1]
  · simp [lowerWeight]
  · intro n _ hn
    simp [lowerWeight,hn]
  · intro h
    exact (h (Finset.mem_insert_self _ _)).elim

/-- Article: normalized lower/upper weights cancel the original common value coefficient exactly. -/
theorem normalizedWeights_cancel (W : DualWeights) (t : ℝ) :
    (∑ n ∈ insert 1 W.lags,(lowerWeight n-upperWeight W (Real.cosh t) n)*Real.sinh (n*t))=0 := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,sum_lowerWeight,sum_upperWeight]
  simp only [Nat.cast_one,one_mul]
  have hsum : (∑ n ∈ W.lags,W.weight n/lagDenominator (Real.cosh t) n*Real.sinh (n*t)) =
      ∑ n ∈ W.lags,W.weight n*Real.sinh t := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← lagDenominator_mul_sinh t n (W.positive_lag n hn)]
    have hD := (lagDenominator_pos (Real.one_le_cosh t) n (W.positive_lag n hn)).ne'
    field_simp
  rw [hsum,← Finset.sum_mul,W.sum_one,one_mul,sub_self]

/-- Article: pointwise g agrees between planar Polyak waves and the polynomial formulation. -/
theorem duality_g_polyak (v : ℝ) (c : Frequency) :
    Duality.g (Waves.polyakMultiplier v) c = g (Real.sinh v) c := by
  unfold Duality.g g
  rw [Waves.polyakMultiplier_normSq]
  ring

/-- Article: pointwise a agrees between planar waves and polynomial lag functionals. -/
theorem duality_a_polyak (v t : ℝ) (n : ℕ) (c : Frequency) :
    Duality.a (Waves.polyakMultiplier v) t n c = lagA (Real.sinh v) t n c := by
  unfold Duality.a lagA lagD
  rw [duality_g_polyak,Waves.chebT_arccos]

/-- Article: pointwise b agrees for every positive lag, including both frequency endpoints. -/
theorem duality_b_polyak (v : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : Frequency) :
    Duality.b (Waves.polyakMultiplier v) n c = lagB (Real.sinh v) n c :=
  Waves.polyak_skew v n hn c

/-- Article: the original strict-certificate symbol is exactly the normalized polynomial
symbol plus the two equal minimizer multipliers. -/
theorem normalizedWeights_symbol (W : DualWeights) (v t γ : ℝ) (c : Frequency) :
    Duality.symbol (Waves.polyakMultiplier v) t (insert 1 W.lags) lowerWeight
      (upperWeight W (Real.cosh t)) γ γ c =
      dualSymbol W (Real.sinh v) (Real.cosh t) c+2*γ*g (Real.sinh v) c := by
  unfold Duality.symbol
  rw [Finset.sum_add_distrib,sum_lowerWeight,sum_upperWeight]
  rw [duality_a_polyak,duality_b_polyak v 1 le_rfl,duality_g_polyak]
  unfold dualSymbol
  have h1 : normalizedLower (Real.sinh v) (Real.cosh t) 1 c =
      lagA (Real.sinh v) t 1 c-lagB (Real.sinh v) 1 c := by
    simp [normalizedLower,lagA,lagD,lagDenominator,chebU,chebT_cosh]
  rw [h1]
  have hs : (∑ n ∈ W.lags,W.weight n/lagDenominator (Real.cosh t) n*
      (Duality.a (Waves.polyakMultiplier v) t n c+Duality.b (Waves.polyakMultiplier v) n c)) =
      ∑ n ∈ W.lags,W.weight n*normalizedUpper (Real.sinh v) (Real.cosh t) n c := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [duality_a_polyak,duality_b_polyak v n (W.positive_lag n hn)]
    unfold normalizedUpper lagA lagD
    rw [chebT_cosh]
    ring
  rw [hs]
  ring

/-- Article: explicit finite strict certificate from the actual normalized polynomial weights.
Use: future linear-gap estimates retain these exact coefficients and lag support. -/
def strictCertificateOfWeights (W : DualWeights) (v t γ ε : ℝ) (hγ : 0 ≤ γ) (hε : 0 < ε)
    (hstrict : ∀ c : Frequency, dualSymbol W (Real.sinh v) (Real.cosh t) c+
      2*γ*g (Real.sinh v) c ≤ -ε) : Duality.StrictCertificate (Waves.polyakMultiplier v) t where
  lags := insert 1 W.lags
  positive_lag n hn := by
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact le_rfl
    · exact W.positive_lag n hn
  α := lowerWeight
  β := upperWeight W (Real.cosh t)
  α_nonneg n _ := by unfold lowerWeight; split_ifs <;> norm_num
  β_nonneg n _ := by
    unfold upperWeight
    split_ifs with hn
    · exact div_nonneg (W.nonneg n hn) (lagDenominator_pos (Real.one_le_cosh t) n (W.positive_lag n hn)).le
    · exact le_rfl
  γplus := γ
  γminus := γ
  γplus_nonneg := hγ
  γminus_nonneg := hγ
  ε := ε
  ε_pos := hε
  cancel := by rw [normalizedWeights_cancel]; ring
  strict c := by rw [normalizedWeights_symbol]; exact hstrict c

end polyak.Boundary
