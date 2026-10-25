import polyak.ModeLocking.TwoLag.DecouplingMaxima
import polyak.Global.Symbols.Normalized
import polyak.Global.Symbols.Slackness
import polyak.Levels.Program.AtomicProgram

/-! The obstruction from independent ratio bounds applies to arbitrary
finite Borel measures, not only to candidate two-atom solutions. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Levels MeasureTheory Set Filter

def pairLags (K : ℕ) : Set ℤ := {1,-(K : ℤ)}

def pairCertificate (Θ : Curve) (K : ℕ) (r : ℝ) (hr : 0≤r) : CertificateSymbol Θ (pairLags K) where
  lags := {1,-(K : ℤ)}
  lags_subset := by simp [pairLags]
  weight n := if n=1 then 1 else r
  weight_nonneg n _ := by split_ifs <;> positivity
  gamma := 0
  gamma_nonneg := le_rfl

theorem pairCertificate_eval (Θ : Curve) {K : ℕ} (hK : 1≤K) (r : ℝ) (hr : 0≤r) (ω : Frequency) :
    (pairCertificate Θ K r hr).eval ω=Θ.lag 1 ω+r*Θ.lag (-(K : ℤ)) ω := by
  have hk : -(K : ℤ)≠1 := by omega
  simp [CertificateSymbol.eval,pairCertificate,hk,Ne.symm hk]

theorem pairCertificate_total (Θ : Curve) {K : ℕ} (hK : 1≤K) (r : ℝ) (hr : 0≤r) :
    Global.Symbols.total (pairCertificate Θ K r hr)=1+r := by
  have hk : -(K : ℤ)≠1 := by omega
  simp [Global.Symbols.total,pairCertificate,hk,Ne.symm hk]

theorem no_solution_of_pair_strict {Θ : Curve} {K : ℕ} (hK : 1≤K) {r : ℝ} (hr : 0≤r)
    (hstrict : ∀ω : Frequency,0<(ω : ℝ)→Θ.lag 1 ω+r*Θ.lag (-(K : ℤ)) ω<0) :
    ¬FPOn Θ (pairLags K) := by
  rintro ⟨w,hw⟩
  let S := pairCertificate Θ K r hr
  have htotal : 0<Global.Symbols.total S := by
    rw [pairCertificate_total Θ hK r hr]
    linarith
  let W := Global.Symbols.normalizeWeights S htotal
  have heval (ω : Frequency) : W.eval Θ ω=(Θ.lag 1 ω+r*Θ.lag (-(K : ℤ)) ω)/(1+r) := by
    rw [Global.Symbols.normalizeWeights_eval,pairCertificate_eval Θ hK r hr,pairCertificate_total Θ hK r hr]
  have hnonpos : ∀ω,W.eval Θ ω≤0 := by
    intro ω
    rw [heval]
    apply div_nonpos_of_nonpos_of_nonneg
    · rcases eq_or_lt_of_le ω.property.1 with h0|h0
      · have hω : ω=frequencyZero := Subtype.ext h0.symm
        simp [hω]
      · exact (hstrict ω h0).le
    · linarith
  have hcarried := W.solution_carried_zero hnonpos hw
  have hz : ∀ᵐω∂w,ω=frequencyZero := by
    filter_upwards [hcarried] with ω hω
    by_contra hn
    have hx : 0<(ω : ℝ) := lt_of_le_of_ne ω.property.1
      (fun he=>hn (Subtype.ext he.symm))
    have he := (div_eq_zero_iff).mp (by rwa [heval] at hω)
    exact (hstrict ω hx).ne (he.resolve_right (by linarith))
  let : IsFiniteMeasure w := hw.1
  let : NeZero w := ⟨hw.2.1⟩
  have hi : (∫ω,Θ.minimizer ω∂w)=∫ _ : Frequency,(-1 : ℝ)∂w := by
    apply integral_congr_ae
    filter_upwards [hz] with ω hω
    rw [hω,Curve.minimizer_at_zero]
  rw [integral_const] at hi
  have hp := measureReal_univ_pos (μ:=w)
  simp only [smul_eq_mul,mul_neg,mul_one] at hi
  linarith [hw.2.2.1]

/-- If the product of independent ratio bounds is below one, a literal
positive two-lag separating symbol exists. -/
theorem strict_pair_of_product_lt_one {Θ : Curve} {K : ℕ}
    (hno : NoCommonNonnegative Θ K) {Rp Rm : ℝ} (hp : 0≤Rp) (hm : 0<Rm)
    (hplus : ∀ω∈plusSet Θ K,plusRatio Θ K ω≤Rp)
    (hminus : ∀ω∈minusSet Θ K,minusRatio Θ K ω≤Rm)
    (hprod : Rp*Rm<1) :
    ∃r : ℝ,0<r ∧ ∀ω : Frequency,0<(ω : ℝ)→Θ.lag 1 ω+r*Θ.lag (-(K : ℤ)) ω<0 := by
  let r := (Rp+1/Rm)/2
  have hr : 0<r := by dsimp [r];positivity
  have hp' : Rp<r := by
    have h : Rp<1/Rm := (lt_div_iff₀ hm).mpr (by simpa using hprod)
    dsimp [r];linarith
  have hm' : r*Rm<1 := by
    dsimp [r]
    field_simp
    nlinarith [hprod]
  refine ⟨r,hr,?_⟩
  intro ω hx
  by_cases h1 : 0<Θ.lag 1 ω
  · have h2 : Θ.lag (-(K : ℤ)) ω<0 :=
      lt_of_not_ge (fun h=>hno ω hx ⟨h1.le,h⟩)
    have hh := (hplus ω ⟨h1,h2⟩).trans_lt hp'
    have he := (div_lt_iff₀ (neg_pos.mpr h2)).mp hh
    nlinarith [he]
  by_cases h2 : 0<Θ.lag (-(K : ℤ)) ω
  · have h1' : Θ.lag 1 ω<0 := lt_of_not_ge (fun h=>hno ω hx ⟨h,h2.le⟩)
    have hh := hminus ω ⟨h2,h1'⟩
    have he := (div_le_iff₀ (neg_pos.mpr h1')).mp hh
    have hmul := mul_le_mul_of_nonneg_left he hr.le
    have hlt := mul_lt_mul_of_pos_right hm' (neg_pos.mpr h1')
    nlinarith [hmul,hlt]
  have hn1 := le_of_not_gt h1
  have hn2 := le_of_not_gt h2
  have hne := hno ω hx
  by_cases hz : Θ.lag 1 ω=0
  · have hneg : Θ.lag (-(K : ℤ)) ω<0 := by
      apply lt_of_le_of_ne hn2
      intro he
      exact hne ⟨by rw [hz],by rw [he]⟩
    rw [hz,zero_add]
    exact mul_neg_of_pos_of_neg hr hneg
  · have hneg : Θ.lag 1 ω<0 := lt_of_le_of_ne hn1 hz
    exact add_neg_of_neg_of_nonpos hneg (mul_nonpos_of_nonneg_of_nonpos hr.le hn2)

end polyak.ModeLocking.TwoLag
