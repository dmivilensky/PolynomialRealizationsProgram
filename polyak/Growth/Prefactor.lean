import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: Appendix C, the final good-window/bad-window argument.
Use: a positive price and strict contraction near its kernel turn the exact
exponential rate into a uniform constant prefactor. The certificate and compact
Gram-cone construction which supplies these hypotheses is a separate argument.
-/

namespace polyak.Growth
noncomputable section

/-- Article: normalized Gram traces are uniformly bounded once bad windows contract.
The constant is explicit and independent of the horizon. -/
theorem normalized_window_bound {a b : ℕ → ℝ} {M B η : ℝ} {p : ℕ}
    (ha : ∀ k,0≤a k) (_hM : 0≤M) (hB : 1≤B) (hη : 0<η) (hp : 0<p)
    (hb0 : b 0≤M*a 0) (hb : ∀ k,b (k+1)≤b k)
    (hshort : ∀ k s : ℕ,s≤p → a (k+s)≤B*a k)
    (hbad : ∀ k,b k≤η*a k → a (k+p)≤a k/2) :
    ∀ k : ℕ,a k≤max B (B*M/η)*a 0 := by
  have hB0 : 0≤B := by linarith
  have hC : 0≤max B (B*M/η) := hB0.trans (le_max_left _ _)
  have hbmono : Antitone b := antitone_nat_of_succ_le hb
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k<p
    · have hh := hshort 0 k (by omega)
      simp only [Nat.zero_add] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (ha 0))
    · let j := k-p
      have hj : j+p=k := Nat.sub_add_cancel (by omega)
      by_cases hprice : b j≤η*a j
      · have hcontract := hbad j hprice
        rw [hj] at hcontract
        have hprev := ih j (by dsimp [j]; omega)
        have hnon : 0≤max B (B*M/η)*a 0 := mul_nonneg hC (ha 0)
        linarith
      · have hgood : η*a j<b j := lt_of_not_ge hprice
        have hprice0 : b j≤b 0 := hbmono (Nat.zero_le j)
        have haj : a j≤M*a 0/η := (le_div_iff₀ hη).mpr (by nlinarith)
        have hlast := hshort j p le_rfl
        rw [hj] at hlast
        calc
          a k≤B*a j := hlast
          _≤B*(M*a 0/η) := mul_le_mul_of_nonneg_left haj hB0
          _=(B*M/η)*a 0 := by ring
          _≤max B (B*M/η)*a 0 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (ha 0)

/-- Article: weighted good/bad windows give the exact uniform exponential prefactor.
Use: w is the actual Gram trace and v is the nonnegative limiting linear price. -/
theorem weighted_window_bound {w v : ℕ → ℝ} {r M B η : ℝ} {p : ℕ}
    (hw : ∀ k,0≤w k) (hr : 0<r) (hM : 0≤M) (hB : 1≤B) (hη : 0<η) (hp : 0<p)
    (hv0 : v 0≤M*w 0) (hv : ∀ k,v (k+1)≤r^2*v k)
    (hshort : ∀ k s : ℕ,s≤p → w (k+s)≤B*r^(2*s)*w k)
    (hbad : ∀ k,v k≤η*w k → w (k+p)≤r^(2*p)*w k/2) :
    ∀ k : ℕ,w k≤max B (B*M/η)*r^(2*k)*w 0 := by
  let a : ℕ → ℝ := fun k => w k/r^(2*k)
  let b : ℕ → ℝ := fun k => v k/r^(2*k)
  have hpow (k s : ℕ) : r^(2*(k+s))=r^(2*k)*r^(2*s) := by
    rw [Nat.mul_add,pow_add]
  have hpos (k : ℕ) : 0<r^(2*k) := pow_pos hr _
  have ha : ∀ k,0≤a k := fun k => div_nonneg (hw k) (hpos k).le
  have hb0 : b 0≤M*a 0 := by simpa only [a,b,mul_zero,pow_zero,div_one] using hv0
  have hb : ∀ k,b (k+1)≤b k := by
    intro k
    dsimp only [b]
    rw [hpow]
    have hh : v (k+1)≤(v k/r^(2*k))*(r^(2*k)*r^(2*1)) := by
      have he : (v k/r^(2*k))*(r^(2*k)*r^(2*1))=r^2*v k := by
        field_simp
      rw [he]
      exact hv k
    exact (div_le_iff₀ (mul_pos (hpos k) (hpos 1))).mpr hh
  have hs : ∀ k s : ℕ,s≤p → a (k+s)≤B*a k := by
    intro k s hsp
    dsimp only [a]
    rw [hpow]
    apply (div_le_iff₀ (mul_pos (hpos k) (hpos s))).mpr
    have he : B*(w k/r^(2*k))*(r^(2*k)*r^(2*s))=B*r^(2*s)*w k := by
      field_simp
    rw [he]
    exact hshort k s hsp
  have hc : ∀ k,b k≤η*a k → a (k+p)≤a k/2 := by
    intro k hk
    have hprice : v k≤η*w k := by
      dsimp only [a,b] at hk
      rwa [← mul_div_assoc,div_le_div_iff_of_pos_right (hpos k)] at hk
    dsimp only [a]
    rw [hpow]
    apply (div_le_iff₀ (mul_pos (hpos k) (hpos p))).mpr
    have he : (w k/r^(2*k)/2)*(r^(2*k)*r^(2*p))=r^(2*p)*w k/2 := by
      field_simp
    rw [he]
    exact hbad k hprice
  have hh := normalized_window_bound ha hM hB hη hp hb0 hb hs hc
  intro k
  have hk := (div_le_iff₀ (hpos k)).mp (hh k)
  simpa only [a,Nat.mul_zero,Nat.zero_mul,pow_zero,div_one,mul_assoc,mul_left_comm,mul_comm] using hk

end
end polyak.Growth
