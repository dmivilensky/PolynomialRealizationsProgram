import polyak.FareyPlateau.FanAnalysis.CompactFamily

/-! An arbitrary set of actual tunings whose slope indices lie in the
source interval gives the compact-family data, without any analytic or
uniformity assumption on the chosen adjacent witnesses. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking Set

def slopeIndex (j k : ℕ) (q : Tuning) : ℝ :=
  2*deriv (TwoLag.phase q (Edge.shift q k (2*Real.pi*j/k))) (2*Real.pi*j/k)

theorem atom_coe_rational {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k) :
    (Edge.atom j k hk hjk:ℝ)=2*Real.pi*j/k := by
  dsimp [Edge.atom,Farey.gridFrequency]
  push_cast
  ring

def intervalAdjacent (q : Tuning) {j k : ℕ} (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b n₁ : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hn : n₁%(k:ℤ)=b)
    (hinterval : (n₁:ℝ)<slopeIndex j k q ∧ slopeIndex j k q<(n₁:ℝ)+k) :
    Edge.AdjacentData q j k where
  period_ge := hk
  numerator_pos := hj
  numerator_lt := hjk
  inverse := b
  inverse_pos := hb0
  inverse_lt := hbk
  inverse_mod := hb
  lower := n₁
  lower_class := hn
  mix := (slopeIndex j k q-n₁)/k
  mix_pos := div_pos (sub_pos.mpr hinterval.1) (by exact_mod_cast (show 0<k by omega))
  mix_lt := (div_lt_one (by exact_mod_cast (show 0<k by omega) : (0:ℝ)<k)).mpr (by linarith [hinterval.2])
  slope := by
    rw [atom_coe_rational]
    change slopeIndex j k q=(n₁:ℝ)+(slopeIndex j k q-n₁)/k*k
    rw [div_mul_cancel₀ _ (by exact_mod_cast (show k≠0 by omega) : (k:ℝ)≠0)]
    ring

def sourceFamily (S : Set Tuning) {j k : ℕ} (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b n₁ : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hn : n₁%(k:ℤ)=b)
    (hinterval : ∀q∈S,(n₁:ℝ)<slopeIndex j k q ∧ slopeIndex j k q<(n₁:ℝ)+k) :
    CompactFamily.Data S j k where
  tuning := Subtype.val
  continuous_tuning := continuous_subtype_val
  adjacent q := intervalAdjacent q.val hk hj hjk b n₁ hb0 hbk hb hn (hinterval q.val q.property)
  lower := n₁
  lower_eq _ := rfl

end polyak.FareyPlateau.FanAnalysis
