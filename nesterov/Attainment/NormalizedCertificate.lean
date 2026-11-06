import nesterov.Attainment.Trace
import nesterov.Duality.Certificate

/-! Every finite strict certificate lies, after exact positive normalization,
in the same compact hull on the whole exponent interval. -/
noncomputable section
open Set
open scoped Topology OnePoint BigOperators
namespace nesterov.Attainment
open Spectral
open nesterov.Duality (symbol)

/-- Article: two minimizer signs and both signs of every finite lag. -/
abbrev CertificateIndices {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s) :=
  Bool ⊕ ((↑cert.lags) × Bool)

/-- Article: unnormalized mass in the compactified symbol family. -/
def certificateMass {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s) :
    CertificateIndices cert → ℝ
  | .inl false => cert.γplus
  | .inl true => cert.γminus
  | .inr (n,false) => cert.α n*Real.sinh ((n : ℕ)*s)
  | .inr (n,true) => cert.β n*Real.sinh ((n : ℕ)*s)

/-- Article: each normalized mass is nonnegative. -/
theorem certificateMass_nonneg {m : SymbolPair} {s : ℝ}
    (cert : StrictCertificate m s) (hs : 0<s) (i : CertificateIndices cert) :
    0 ≤ certificateMass cert i := by
  rcases i with b | ⟨n,b⟩ <;> cases b
  · exact cert.γplus_nonneg
  · exact cert.γminus_nonneg
  · exact mul_nonneg (cert.α_nonneg n n.property)
      (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n n.property)) hs)).le
  · exact mul_nonneg (cert.β_nonneg n n.property)
      (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n n.property)) hs)).le

/-- Article: strict separation forces positive total mass. Use: justify normalization without an assumed nonzero certificate. -/
theorem certificateMass_sum_pos {m : SymbolPair} {s : ℝ}
    (cert : StrictCertificate m s) (hs : 0<s) : 0<∑ i,certificateMass cert i := by
  have hnonneg : 0 ≤ ∑ i,certificateMass cert i := Finset.sum_nonneg (fun i _ => certificateMass_nonneg cert hs i)
  by_contra hnot
  have hz : ∑ i,certificateMass cert i=0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hall : ∀ i,certificateMass cert i=0 := by
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => certificateMass_nonneg cert hs i)).mp hz i
      (Finset.mem_univ _)
  have hgp : cert.γplus=0 := hall (.inl false)
  have hgm : cert.γminus=0 := hall (.inl true)
  have hα (n : ℕ) (hn : n∈cert.lags) : cert.α n=0 := by
    have he := hall (.inr (⟨n,hn⟩,false))
    have hp := Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n hn)) hs)
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
  have hβ (n : ℕ) (hn : n∈cert.lags) : cert.β n=0 := by
    have he := hall (.inr (⟨n,hn⟩,true))
    have hp := Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n hn)) hs)
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
  let c : Frequency := ⟨0,by norm_num⟩
  have hsym : symbol m s cert.lags cert.α cert.β cert.γplus cert.γminus c=0 := by
    unfold symbol
    rw [hgp,hgm]
    simp only [zero_mul,add_zero]
    apply Finset.sum_eq_zero
    intro n hn
    rw [hα n hn,hβ n hn]
    ring
  have hbad := cert.strict c
  rw [hsym] at hbad
  linarith [cert.ε_pos]

def polynomialDualFamily (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) (δ : ℝ) :=
  dualFamily lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) δ

def polynomialDualHull (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) :=
  dualHull lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)

def certificateGenerator {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) : CertificateIndices cert → DualPoint lo hi
  | .inl false => polynomialDualFamily u p lo hi σ hlo 1 ∞
  | .inl true => polynomialDualFamily u p lo hi σ hlo (-1) ∞
  | .inr (n,false) => polynomialDualFamily u p lo hi σ hlo 1 ((n.val-1 : ℕ) : OnePoint ℕ)
  | .inr (n,true) => polynomialDualFamily u p lo hi σ hlo (-1) ((n.val-1 : ℕ) : OnePoint ℕ)

theorem certificateGenerator_mem {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) (i : CertificateIndices cert) :
    certificateGenerator cert u p lo hi σ hlo i ∈
      dualGenerators lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ) := by
  rcases i with b | ⟨n,b⟩ <;> cases b
  · exact ⟨(false,∞),rfl⟩
  · exact ⟨(true,∞),rfl⟩
  · exact ⟨(false,((n.val-1 : ℕ) : OnePoint ℕ)),rfl⟩
  · exact ⟨(true,((n.val-1 : ℕ) : OnePoint ℕ)),rfl⟩

def evaluateReal (lo hi : ℝ) (hlo : 0 < lo) (s : LagParameter lo hi) (c : Frequency) :
    DualPoint lo hi →ₗ[ℝ] ℝ := (traceCLM lo hi s (physicalAngle lo hlo c)).toLinearMap

theorem evaluateReal_star {m : SymbolPair} {s' : ℝ} (cert : StrictCertificate m s')
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (c : Frequency) (b : Bool) :
    evaluateReal lo hi hlo s c (certificateGenerator cert u p lo hi σ hlo (.inl b)) =
      g (polynomialPair u p (σ*s)) c := by
  cases b <;> change ((dualFamily lo hi hlo (gapEntireMap u p lo hi σ)
    (skewEntireMap u p lo hi σ) _ ∞).2 (s,physicalAngle lo hlo c)).re = _
  all_goals rw [dualFamily_physical_infty]
  all_goals rfl

theorem evaluateReal_lag {m : SymbolPair} {s' : ℝ} (cert : StrictCertificate m s')
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (c : Frequency) (n : ↑cert.lags) (b : Bool) :
    evaluateReal lo hi hlo s c (certificateGenerator cert u p lo hi σ hlo (.inr (n,b))) =
      (if b then (lagA (polynomialPair u p (σ*s)) s n c+lagB (polynomialPair u p (σ*s)) n c)/Real.sinh ((n : ℕ)*s)
        else (lagA (polynomialPair u p (σ*s)) s n c-lagB (polynomialPair u p (σ*s)) n c)/Real.sinh ((n : ℕ)*s)) := by
  have hn : n.val-1+1=n.val := Nat.sub_add_cancel (cert.positive_lag n n.property)
  cases b <;> change ((dualFamily lo hi hlo (gapEntireMap u p lo hi σ)
    (skewEntireMap u p lo hi σ) _ ((n.val-1 : ℕ) : OnePoint ℕ)).2
      (s,physicalAngle lo hlo c)).re = _
  all_goals rw [dualFamily_physical_coe,hn]
  all_goals simp only [Complex.ofReal_re,one_mul,neg_one_mul,sub_neg_eq_add,
    Bool.false_eq_true,↓reduceIte]

/-- Article: the common C charge of each signed generator. -/
def certificateSign {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s) : CertificateIndices cert → ℝ
  | .inl b => if b then -1 else 1
  | .inr (_,b) => if b then -1 else 1

/-- Article: exact generator charge. -/
theorem certificateGenerator_charge {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) (i : CertificateIndices cert) :
    (certificateGenerator cert u p lo hi σ hlo i).1=certificateSign cert i := by
  rcases i with b | ⟨n,b⟩ <;> cases b <;> rfl

/-- Article: the unnormalized finite dual combination. -/
def certificateCombination {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) : DualPoint lo hi := ∑ i,certificateMass cert i • certificateGenerator cert u p lo hi σ hlo i

/-- Article: raw certificate cancellation survives radial normalization exactly. -/
theorem certificateCombination_charge {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) : (certificateCombination cert u p lo hi σ hlo).1=0 := by
  unfold certificateCombination
  rw [Prod.fst_sum]
  simp only [Prod.smul_fst,certificateGenerator_charge,smul_eq_mul,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,certificateMass,certificateSign,
    Bool.false_eq_true,↓reduceIte,mul_neg_one,mul_one]
  have hsum : (∑ n : ↑cert.lags, (-(cert.β n*Real.sinh ((n : ℕ)*s))+cert.α n*Real.sinh ((n : ℕ)*s)))=
      ∑ n ∈ cert.lags,(cert.α n-cert.β n)*Real.sinh (n*s) := by
    calc
      _ = ∑ n : ↑cert.lags,(cert.α n-cert.β n)*Real.sinh ((n : ℕ)*s) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := Finset.sum_coe_sort cert.lags
        (fun n : ℕ => (cert.α n-cert.β n)*Real.sinh ((n : ℝ)*s))

  rw [hsum]
  linarith [cert.cancel]

/-- Article: radial normalization preserves the actual raw symbol. -/
theorem evaluateReal_combination (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (cert : StrictCertificate (polynomialPair u p (σ*s)) s)
    (c : Frequency) :
    evaluateReal lo hi hlo s c (certificateCombination cert u p lo hi σ hlo) =
      symbol (polynomialPair u p (σ*s)) s cert.lags cert.α cert.β cert.γplus cert.γminus c := by
  unfold certificateCombination
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
    certificateMass,evaluateReal_star,evaluateReal_lag,Bool.false_eq_true,↓reduceIte]
  have hsum : (∑ n : ↑cert.lags,(
      (cert.β n*Real.sinh ((n : ℕ)*s))*((lagA (polynomialPair u p (σ*s)) s n c+lagB (polynomialPair u p (σ*s)) n c)/Real.sinh ((n : ℕ)*s))+
      (cert.α n*Real.sinh ((n : ℕ)*s))*((lagA (polynomialPair u p (σ*s)) s n c-lagB (polynomialPair u p (σ*s)) n c)/Real.sinh ((n : ℕ)*s))))=
      ∑ n ∈ cert.lags,(cert.α n*(lagA (polynomialPair u p (σ*s)) s n c-lagB (polynomialPair u p (σ*s)) n c)+cert.β n*(lagA (polynomialPair u p (σ*s)) s n c+lagB (polynomialPair u p (σ*s)) n c)) := by
    calc
      _ = ∑ n : ↑cert.lags,(cert.α n*(lagA (polynomialPair u p (σ*s)) s n c-lagB (polynomialPair u p (σ*s)) n c)+cert.β n*(lagA (polynomialPair u p (σ*s)) s n c+lagB (polynomialPair u p (σ*s)) n c)) := by
        apply Finset.sum_congr rfl
        intro n _
        have hp : Real.sinh ((n : ℕ)*s)≠0 := ne_of_gt
          (Real.sinh_pos_iff.mpr (mul_pos (Nat.cast_pos.mpr (cert.positive_lag n n.property)) (hlo.trans_le s.property.1)))
        field_simp
        ring
      _ = _ := Finset.sum_coe_sort cert.lags
        (fun n : ℕ => cert.α n*(lagA (polynomialPair u p (σ*s)) s n c-lagB (polynomialPair u p (σ*s)) n c)+cert.β n*(lagA (polynomialPair u p (σ*s)) s n c+lagB (polynomialPair u p (σ*s)) n c))

  rw [hsum]
  unfold symbol
  ring

def normalizedCertificate {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) : DualPoint lo hi :=
  (∑ i,certificateMass cert i)⁻¹ • certificateCombination cert u p lo hi σ hlo

theorem normalizedCertificate_mem {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (hs : 0 < s) (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) :
    normalizedCertificate cert u p lo hi σ hlo ∈ polynomialDualHull u p lo hi σ hlo := by
  have hp' := certificateMass_sum_pos cert hs
  have he : normalizedCertificate cert u p lo hi σ hlo =
      ∑ i,(certificateMass cert i/(∑ j,certificateMass cert j)) • certificateGenerator cert u p lo hi σ hlo i := by
    unfold normalizedCertificate certificateCombination
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  rw [he]
  apply sum_mem_dualHull
  · intro i
    exact div_nonneg (certificateMass_nonneg cert hs i) hp'.le
  · rw [← Finset.sum_div,div_self (ne_of_gt hp')]
  · exact certificateGenerator_mem cert u p lo hi σ hlo

theorem normalizedCertificate_charge {m : SymbolPair} {s : ℝ} (cert : StrictCertificate m s)
    (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo) :
    (normalizedCertificate cert u p lo hi σ hlo).1=0 := by
  simp only [normalizedCertificate,Prod.smul_fst,certificateCombination_charge,smul_zero]

theorem normalizedCertificate_evaluate (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (cert : StrictCertificate (polynomialPair u p (σ*s)) s) (c : Frequency) :
    ((normalizedCertificate cert u p lo hi σ hlo).2 (s,physicalAngle lo hlo c)).re =
      symbol (polynomialPair u p (σ*s)) s cert.lags cert.α cert.β cert.γplus cert.γminus c /
        (∑ i,certificateMass cert i) := by
  change evaluateReal lo hi hlo s c (normalizedCertificate cert u p lo hi σ hlo)=_
  rw [normalizedCertificate,map_smul,evaluateReal_combination]
  simp only [smul_eq_mul]
  ring

theorem exists_normalized_dual (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s : LagParameter lo hi) (cert : StrictCertificate (polynomialPair u p (σ*s)) s) :
    ∃ d ∈ polynomialDualHull u p lo hi σ hlo, d.1=0 ∧
      ∀ c : Frequency, (d.2 (s,physicalAngle lo hlo c)).re ≤ 0 := by
  refine ⟨normalizedCertificate cert u p lo hi σ hlo,
    normalizedCertificate_mem cert (hlo.trans_le s.property.1) u p lo hi σ hlo,
    normalizedCertificate_charge cert u p lo hi σ hlo, fun c => ?_⟩
  rw [normalizedCertificate_evaluate]
  exact div_nonpos_of_nonpos_of_nonneg (le_trans (cert.strict c) (neg_nonpos.mpr cert.ε_pos.le))
    (certificateMass_sum_pos cert (hlo.trans_le s.property.1)).le

end nesterov.Attainment
