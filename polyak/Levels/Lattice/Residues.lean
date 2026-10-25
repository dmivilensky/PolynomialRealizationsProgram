import polyak.Levels.Lattice.Farey
import polyak.Levels.Program.Curve

/-! Exact first-violation arithmetic for signed rational lags. The residue
is the nonnegative integer remainder, so negative upper lags require no
separate convention. -/
noncomputable section
namespace polyak.Levels.Lattice

/-- Periodic reduction retains the original signed lag. -/
theorem rational_lag_reduce {k : ℕ} (hk : 0<k) (j : ℕ) (n : ℤ) (θ : ℝ) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))=
      lagValue θ (2*Real.pi*((n*(j:ℤ))%(k:ℤ):ℤ)/k) := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have he : (n*(j:ℤ):ℝ)=(((n*(j:ℤ))%(k:ℤ):ℤ):ℝ)+
      (((n*(j:ℤ))/(k:ℤ):ℤ):ℝ)*(k:ℝ) := by
    exact_mod_cast (Int.emod_add_ediv_mul (n*(j:ℤ)) (k:ℤ)).symm
  unfold lagValue
  have hphase : (n:ℝ)*(2*Real.pi*j/k)-θ=
      (2*Real.pi*((n*(j:ℤ))%(k:ℤ):ℤ)/k-θ)+
      ((n*(j:ℤ))/(k:ℤ):ℤ)*(2*Real.pi) := by
    push_cast at he ⊢
    field_simp
    linear_combination (2*Real.pi)*he
  rw [hphase,Real.cos_add_int_mul_two_pi]

theorem rational_lag_neg_iff {k : ℕ} (hk : 0<k) (j : ℕ) (n : ℤ)
    {θ : ℝ} (hθ : 0<θ) (hθπ : θ≤Real.pi) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))<0 ↔
      0<(n*(j:ℤ))%(k:ℤ) ∧ (((n*(j:ℤ))%(k:ℤ):ℤ):ℝ)<(k:ℝ)*θ/Real.pi := by
  have hkZ : (0:ℤ)<k := by exact_mod_cast hk
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hr0 : (0:ℝ)≤((n*(j:ℤ))%(k:ℤ):ℤ) := by
    exact_mod_cast Int.emod_nonneg (n*(j:ℤ)) hkZ.ne'
  have hrk : (((n*(j:ℤ))%(k:ℤ):ℤ):ℝ)<k := by
    exact_mod_cast Int.emod_lt_of_pos (n*(j:ℤ)) hkZ
  rw [rational_lag_reduce hk j n,
    lagValue_neg_iff hθ hθπ (by positivity) (by
      apply (div_lt_iff₀ hkR).mpr
      nlinarith [Real.pi_pos])]
  have he : (2*Real.pi*((n*(j:ℤ))%(k:ℤ):ℤ)/k<2*θ) ↔
      (((n*(j:ℤ))%(k:ℤ):ℤ):ℝ)<(k:ℝ)*θ/Real.pi := by
    rw [div_lt_iff₀ hkR,lt_div_iff₀ Real.pi_pos]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨?_,hb⟩
    have hh : (0:ℝ)<((n*(j:ℤ))%(k:ℤ):ℤ) := by
      have hmul:0<2*Real.pi*(((n*(j:ℤ))%(k:ℤ):ℤ):ℝ) := by simpa only [zero_mul] using (lt_div_iff₀ hkR).mp ha
      nlinarith [Real.pi_pos]
    exact_mod_cast hh
  · rintro ⟨ha,hb⟩
    have hh : (0:ℝ)<((n*(j:ℤ))%(k:ℤ):ℤ) := by exact_mod_cast ha
    exact ⟨by positivity,hb⟩

/-- Literal integer range 1,...,ceil(k theta/pi)-1, including both threshold
endpoints and negative original lag indices. -/
theorem rational_lag_neg_iff_ceil {k : ℕ} (hk : 0<k) (j : ℕ) (n : ℤ)
    {θ : ℝ} (hθ : 0<θ) (hθπ : θ≤Real.pi) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))<0 ↔
      1≤(n*(j:ℤ))%(k:ℤ) ∧
        (n*(j:ℤ))%(k:ℤ)≤⌈(k:ℝ)*θ/Real.pi⌉-1 := by
  rw [rational_lag_neg_iff hk j n hθ hθπ,←Int.lt_ceil]
  omega

/-- Immediately beyond the first threshold, residue one is the complete
set of violations, not merely one selected bad lag. -/
theorem first_violations {k : ℕ} (hk : 0<k) (j : ℕ) (n : ℤ)
    {θ : ℝ} (hθ : Real.pi/k<θ) (hθ₂ : θ≤2*Real.pi/k) (hθπ : θ≤Real.pi) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))<0 ↔ (n*(j:ℤ))%(k:ℤ)=1 := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hθ0 : 0<θ := (div_pos Real.pi_pos hkR).trans hθ
  have hlo : 1<(k:ℝ)*θ/Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    have hh:Real.pi<θ*(k:ℝ) := (div_lt_iff₀ hkR).mp hθ
    nlinarith
  have hhi : (k:ℝ)*θ/Real.pi≤2 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    have hh:θ*(k:ℝ)≤2*Real.pi := (le_div_iff₀ hkR).mp hθ₂
    nlinarith
  rw [rational_lag_neg_iff hk j n hθ0 hθπ]
  constructor
  · rintro ⟨ha,hb⟩
    have hh : (((n*(j:ℤ))%(k:ℤ):ℤ):ℝ)<2 := hb.trans_le hhi
    have hhZ : (n*(j:ℤ))%(k:ℤ)<2 := by exact_mod_cast hh
    omega
  · intro he
    rw [he]
    exact ⟨by norm_num,by simpa only [Int.cast_one] using hlo⟩

/-- The article's lattice sign theorem for every curve and every integer lag. -/
theorem curve_signed_lag_neg_iff (Θ : Curve) (ω : Frequency) (n : ℤ) :
    Θ.lag n ω<0 ↔ ∃ l : ℤ,
      0<(n:ℝ)*xi (ω:ℝ) (Θ ω)-l*eta (Θ ω) ∧
      (n:ℝ)*xi (ω:ℝ) (Θ ω)-l*eta (Θ ω)<1 :=
  signed_lag_neg_iff (Θ.pos ω) (Θ.le_pi ω) n

end polyak.Levels.Lattice
