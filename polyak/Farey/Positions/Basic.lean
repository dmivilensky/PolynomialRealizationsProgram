import polyak.Levels.Lattice.Residues

/-! Signed positions on a rational frequency grid. -/
noncomputable section
namespace polyak.Farey

def positionValue (k : ℤ) (a ρ : ℝ) : ℝ :=
  2 * Real.sin (Real.pi * ρ / k) * Real.sin (Real.pi * (ρ-a) / k)

@[simp] theorem positionValue_zero (k : ℤ) (a : ℝ) : positionValue k a 0=0 := by
  simp [positionValue]

@[simp] theorem positionValue_self (k : ℤ) (a : ℝ) : positionValue k a a=0 := by
  simp [positionValue]

theorem positionValue_neg_iff {k : ℤ} {a ρ : ℝ} (hk : 0<k)
    (ha : 0<a) (hak : a≤k) (hρ : 0<ρ) (hρk : ρ<k) :
    positionValue k a ρ<0 ↔ ρ<a := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hs : 0<Real.sin (Real.pi*ρ/k) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos (mul_pos Real.pi_pos hρ) hkr)
    ((div_lt_iff₀ hkr).mpr (by nlinarith [Real.pi_pos]))
  have hlo : -Real.pi<Real.pi*(ρ-a)/k :=
    (lt_div_iff₀ hkr).mpr (by nlinarith [Real.pi_pos])
  have hhi : Real.pi*(ρ-a)/k<Real.pi :=
    (div_lt_iff₀ hkr).mpr (by nlinarith [Real.pi_pos])
  constructor
  · intro hh
    have hn : Real.sin (Real.pi*(ρ-a)/k)<0 := by dsimp [positionValue] at hh; nlinarith
    by_contra h
    have hp := Real.sin_nonneg_of_nonneg_of_le_pi
      (div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr (le_of_not_gt h))) hkr.le) hhi.le
    linarith
  · intro hh
    have hn := Real.sin_neg_of_neg_of_neg_pi_lt
      (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos (sub_neg.mpr hh)) hkr) hlo
    dsimp [positionValue]
    nlinarith

theorem positionValue_pos_iff {k : ℤ} {a ρ : ℝ} (hk : 0<k)
    (ha : 0<a) (hak : a≤k) (hρ : 0<ρ) (hρk : ρ<k) :
    0<positionValue k a ρ ↔ a<ρ := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hs : 0<Real.sin (Real.pi*ρ/k) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos (mul_pos Real.pi_pos hρ) hkr)
    ((div_lt_iff₀ hkr).mpr (by nlinarith [Real.pi_pos]))
  have hlo : -Real.pi<Real.pi*(ρ-a)/k :=
    (lt_div_iff₀ hkr).mpr (by nlinarith [Real.pi_pos])
  have hhi : Real.pi*(ρ-a)/k<Real.pi :=
    (div_lt_iff₀ hkr).mpr (by nlinarith [Real.pi_pos])
  constructor
  · intro hh
    have hn : 0<Real.sin (Real.pi*(ρ-a)/k) := by dsimp [positionValue] at hh; nlinarith
    by_contra h
    have hp := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le
        (sub_nonpos.mpr (le_of_not_gt h))) hkr.le) hlo.le
    linarith
  · intro hh
    have hn := Real.sin_pos_of_pos_of_lt_pi
      (div_pos (mul_pos Real.pi_pos (sub_pos.mpr hh)) hkr) hhi
    dsimp [positionValue]
    positivity

theorem positionValue_eq_zero_iff {k : ℤ} {a ρ : ℝ} (hk : 0<k)
    (ha : 0<a) (hak : a≤k) (hρ : 0<ρ) (hρk : ρ<k) :
    positionValue k a ρ=0 ↔ ρ=a := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hr
    · have := (positionValue_neg_iff hk ha hak hρ hρk).mpr hl; linarith
    · have := (positionValue_pos_iff hk ha hak hρ hρk).mpr hr; linarith
  · rintro rfl
    simp [positionValue]

def gridFrequency (k i : ℤ) (hk : 0 < k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) :
    Levels.Frequency :=
  ⟨2*Real.pi*i/k, by
    have hkr : (0:ℝ)<k := by exact_mod_cast hk
    have hir : (0:ℝ) ≤ i := by exact_mod_cast hi
    have hikr : (2:ℝ)*i≤k := by exact_mod_cast hik
    exact ⟨by positivity, (div_le_iff₀ hkr).mpr (by nlinarith [Real.pi_pos])⟩⟩

@[simp] theorem gridFrequency_val (k i : ℤ) (hk : 0 < k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) :
    (gridFrequency k i hk hi hik : ℝ)=2*Real.pi*i/k := rfl

def gridPhase (Θ : Levels.Curve) (k i : ℤ) (hk : 0 < k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) : ℝ :=
  k * Θ (gridFrequency k i hk hi hik) / Real.pi

theorem gridPhase_pos (Θ : Levels.Curve) (k i : ℤ) (hk : 0 < k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) :
    0<gridPhase Θ k i hk hi hik := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  exact div_pos (mul_pos hkr (Θ.pos _)) Real.pi_pos

theorem gridPhase_le (Θ : Levels.Curve) (k i : ℤ) (hk : 0 < k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) :
    gridPhase Θ k i hk hi hik≤k := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  dsimp [gridPhase]
  exact (div_le_iff₀ Real.pi_pos).mpr (by nlinarith [Θ.le_pi (gridFrequency k i hk hi hik)])

theorem signed_lag_reduce (k i n : ℤ) (hk : k≠0) (θ : ℝ) :
    Levels.Lattice.lagValue θ ((n:ℝ)*(2*Real.pi*i/k)) =
      Levels.Lattice.lagValue θ (2*Real.pi*(((n*i)%k:ℤ):ℝ)/k) := by
  have hkr : (k:ℝ)≠0 := by exact_mod_cast hk
  have he : ((n*i:ℤ):ℝ)=((n*i)%k:ℤ)+(k:ℝ)*((n*i)/k:ℤ) := by
    exact_mod_cast (by simpa [mul_comm] using (Int.emod_add_ediv_mul (n*i) k).symm : n*i = (n*i)%k+k*((n*i)/k))
  have he' : (n:ℝ)*(2*Real.pi*i/k)-θ =
      (2*Real.pi*(((n*i)%k:ℤ):ℝ)/k-θ)+(((n*i)/k:ℤ):ℝ)*(2*Real.pi) := by
    push_cast at he
    field_simp
    linear_combination 2*Real.pi*he
  unfold Levels.Lattice.lagValue
  rw [he',Real.cos_add_int_mul_two_pi]

theorem lag_at_grid_eq_positionValue (Θ : Levels.Curve) (k i n : ℤ)
    (hk : 0 < k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) :
    Θ.lag n (gridFrequency k i hk hi hik)=
      positionValue k (gridPhase Θ k i hk hi hik) (((n*i)%k:ℤ):ℝ) := by
  change Levels.Lattice.lagValue (Θ (gridFrequency k i hk hi hik))
    ((n:ℝ)*(2*Real.pi*i/k))=_
  rw [signed_lag_reduce k i n (ne_of_gt hk),Levels.Lattice.lagValue_eq_sines]
  have hkr : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
  unfold positionValue gridPhase
  congr 2 <;> field_simp

end polyak.Farey
