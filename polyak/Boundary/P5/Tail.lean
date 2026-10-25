import polyak.Boundary.P5.TailOscillation

/-!
Article: Lemma p5tail, all lags n≥24 near the three-cycle.
Use: uniform strict primal feasibility as h tends to zero.
Proof: the source amplitude and phase bounds perturb the exact three-cycle
by O(h+nh), whereas the radial contribution is at least 0.49n²h.
-/

noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: the actual averaged minimizer slack of the two-atom spectrum. -/
def twoAtomGap (u p : ℝ) (x y : Frequency) : ℝ := (1-p)*g u x+p*g u y

/-- Article: the actual signed raw primal slack, including d=C sinh t. -/
def twoAtomRaw (u G p d : ℝ) (n : ℕ) (σ : ℝ) (x y : Frequency) : ℝ :=
  (1-p)*actualRaw u G n σ x+p*actualRaw u G n σ y-σ*d*lagDenominator G n

/-- Article: the concrete inequalities (centralbounds), after p=hP and d=hD.
All fields are source parameter or amplitude bounds; no feasibility conclusion is assumed. -/
structure TailBounds (h u p d : ℝ) (x y : Frequency) : Prop where
  h_pos : 0 < h
  h_le : h ≤ 59/2500
  u_nonneg : 0 ≤ u
  u_lt : u < 11/20
  p_nonneg : 0 ≤ p
  p_le : p ≤ 3*h
  d_nonneg : 0 ≤ d
  d_le : d ≤ (11/5)*h
  gap_gt : 49/100 < twoAtomGap u p x y
  star_gt : 1/4 < twoAtomGap u p x y-|d/Real.sinh (Real.arcosh (1+h))|
  main_gap : |g u x-1/2| < h
  mean_gap : |twoAtomGap u p x y-1/2| < 2*h
  amplitude : |2*u*Real.sin (Real.arccos x)-Real.sqrt 3/2| < 2*h
  phase : |Real.arccos (x : ℝ)-2*Real.pi/3| < h/3

theorem TailBounds.p_le_one {h u p d : ℝ} {x y : Frequency} (hb : TailBounds h u p d x y) : p ≤ 1 := by
  linarith [hb.p_le,hb.h_le]

theorem TailBounds.gap_le_one {h u p d : ℝ} {x y : Frequency} (hb : TailBounds h u p d x y) :
    twoAtomGap u p x y ≤ 1 := by
  have hx : g u x ≤ 1 := by unfold g; nlinarith [sq_nonneg u,sq_nonneg (x : ℝ)]
  have hy : g u y ≤ 1 := by unfold g; nlinarith [sq_nonneg u,sq_nonneg (y : ℝ)]
  have h₀ := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hb.p_le_one)
  have h₁ := mul_le_mul_of_nonneg_left hy hb.p_nonneg
  unfold twoAtomGap
  nlinarith

/-- Article: exact radial/oscillatory decomposition of the two-atom slack. -/
theorem twoAtomRaw_eq (u p d t : ℝ) (n : ℕ) (σ : ℝ) (x y : Frequency) :
    twoAtomRaw u (Real.cosh t) p d n σ x y =
      twoAtomGap u p x y*Real.cosh (n*t)-
      ((1-p)*tailOsc u n σ x+p*tailOsc u n σ y)-σ*d*lagDenominator (Real.cosh t) n := by
  unfold twoAtomRaw twoAtomGap actualRaw tailOsc
  rw [chebT_cosh]
  ring

/-- Article: the uniform raw tail bound for a two-atom mixture. -/
theorem twoAtomRaw_tail {u p d t : ℝ} {x y : Frequency} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ht : 0 < t) (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    (twoAtomGap u p x y-|d/Real.sinh t|)*Real.cosh (n*t)-(twoAtomGap u p x y+2*u^2) ≤
      twoAtomRaw u (Real.cosh t) p d n σ x y := by
  have hδ : -σ=1 ∨ -σ= -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hat (c : Frequency) :
      g u c*Real.cosh (n*t)-(g u c+2*u^2) ≤ actualRaw u (Real.cosh t) n σ c := by
    have he := pointwise_lag_tail u t n hn c (-σ) hδ
    simpa only [actualRaw,chebT_cosh,lagA,lagD,neg_mul,sub_neg_eq_add] using he
  have hx := mul_le_mul_of_nonneg_left (hat x) (sub_nonneg.mpr hp1)
  have hy := mul_le_mul_of_nonneg_left (hat y) hp
  have hsh := Real.sinh_pos_iff.mpr ht
  have hid : d*lagDenominator (Real.cosh t) n=d/Real.sinh t*Real.sinh (n*t) := by
    rw [← lagDenominator_mul_sinh t n hn]
    field_simp [hsh.ne']
  have hs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  have hab : σ*d*lagDenominator (Real.cosh t) n ≤ |d/Real.sinh t| * Real.cosh (n*t) := by
    calc
      σ*d*lagDenominator (Real.cosh t) n ≤ |σ*d*lagDenominator (Real.cosh t) n| := le_abs_self _
      _ = |d/Real.sinh t| * |Real.sinh (n*t)| := by
        rw [mul_assoc,hid,abs_mul,hs,one_mul,abs_mul]
      _ ≤ |d/Real.sinh t| * Real.cosh (n*t) :=
        mul_le_mul_of_nonneg_left (abs_sinh_le_cosh _) (abs_nonneg _)
  unfold twoAtomRaw twoAtomGap
  nlinarith

/-- Article: every lag with nt≥3 is strictly feasible under the source bounds. -/
theorem twoAtomRaw_pos_large {h u p d : ℝ} {x y : Frequency} (hb : TailBounds h u p d x y)
    (n : ℕ) (hn : 1 ≤ n) (hnt : 3 ≤ n*Real.arcosh (1+h))
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    0 < twoAtomRaw u (1+h) p d n σ x y := by
  let t := Real.arcosh (1+h)
  have ht : 0 < t := Real.arcosh_pos (by linarith [hb.h_pos])
  have hG : Real.cosh t=1+h := Real.cosh_arcosh (by linarith [hb.h_pos])
  have ht' : 0 ≤ (n : ℝ)*t := by positivity
  have hcosh : 10 < Real.cosh (n*t) := by
    have hm : Real.cosh 3 ≤ Real.cosh (n*t) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),abs_of_nonneg ht']
      exact hnt
    exact hyperbolic_three_bounds.1.trans_le hm
  have htail := twoAtomRaw_tail (u:=u) (d:=d) (x:=x) (y:=y) hb.p_nonneg hb.p_le_one ht n hn σ hσ
  rw [hG] at htail
  have hgap := mul_lt_mul_of_pos_right hb.star_gt (Real.cosh_pos (n*t))
  have hquarter := mul_lt_mul_of_pos_left hcosh (by norm_num : (0 : ℝ) < 1/4)
  have hu2 : u^2 ≤ (11/20 : ℝ)^2 :=
    (sq_le_sq₀ hb.u_nonneg (by norm_num)).mpr hb.u_lt.le
  have hmax := hb.gap_le_one
  dsimp only [t] at *
  nlinarith

/-- Article: the explicit polynomial remaining after the small-nt perturbation. -/
theorem tail_polynomial_pos (n : ℕ) (hn : 24 ≤ n) :
    0 < (49/100 : ℝ)*(n : ℝ)^2-9*n-17 := by
  have hn' : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := mul_nonneg (by linarith : 0 ≤ (n : ℝ)-24)
    (by linarith : 0 ≤ (49/100 : ℝ)*n+(69/25 : ℝ))
  nlinarith

/-- Article: every lag with nt≤3 is strictly feasible, uniformly as h↓0. -/
theorem twoAtomRaw_pos_small {h u p d : ℝ} {x y : Frequency} (hb : TailBounds h u p d x y)
    (n : ℕ) (hn : 24 ≤ n) (hnt : n*Real.arcosh (1+h) ≤ 3)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    0 < twoAtomRaw u (1+h) p d n σ x y := by
  let t := Real.arcosh (1+h)
  have ht : 0 < t := Real.arcosh_pos (by linarith [hb.h_pos])
  have hG : Real.cosh t=1+h := Real.cosh_arcosh (by linarith [hb.h_pos])
  have hn1 : 1 ≤ n := by omega
  have hrad := cosh_nat_lower t n
  rw [hG] at hrad
  have hrad' : (n : ℝ)^2*h ≤ Real.cosh (n*t)-1 := by nlinarith [hrad]
  have hg : 0 ≤ twoAtomGap u p x y := by linarith [hb.gap_gt]
  have hrad₀ := mul_le_mul_of_nonneg_left hrad' hg
  have hrad₁ := mul_le_mul_of_nonneg_right hb.gap_gt.le
    (mul_nonneg (sq_nonneg (n : ℝ)) hb.h_pos.le)
  have hosc := mixed_oscillation_change (y:=y) hb.h_pos.le hb.u_nonneg hb.u_lt.le
    hb.p_nonneg hb.p_le hb.main_gap.le hb.amplitude.le hb.phase.le n hn1 σ hσ
  have hosc' := (le_abs_self ((1-p)*tailOsc u n σ x+p*tailOsc u n σ y-cycleOsc n σ)).trans hosc
  have hmean := (abs_le.mp hb.mean_gap.le).1
  have hcycle := cycle_raw_nonneg n hn1 σ hσ
  have hden := lagDenominator_pos (by linarith [hb.h_pos] : (1 : ℝ) ≤ 1+h) n hn1
  have hden' := lagDenominator_le_three ht n hn1 hnt
  rw [hG] at hden'
  have hd₀ := mul_le_mul_of_nonneg_left hden' hb.d_nonneg
  have hd₁ := mul_le_mul_of_nonneg_right hb.d_le
    (show 0 ≤ (7/2 : ℝ)*n by positivity)
  have hd : d*lagDenominator (1+h) n ≤ (77/10 : ℝ)*n*h := by nlinarith
  have hsd : σ*d*lagDenominator (1+h) n ≤ (77/10 : ℝ)*n*h := by
    have hp := mul_nonneg hb.d_nonneg hden.le
    rcases hσ with rfl | rfl <;> norm_num at * <;> nlinarith
  have hid := twoAtomRaw_eq u p d t n σ x y
  rw [hG] at hid
  have hpoly := mul_pos hb.h_pos (tail_polynomial_pos n hn)
  have hnh : 0 ≤ (n : ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hb.h_pos.le
  nlinarith

/-- Article: Lemma p5tail, with every actual raw lag n≥24 covered. -/
theorem twoAtomRaw_pos_of_tailBounds {h u p d : ℝ} {x y : Frequency}
    (hb : TailBounds h u p d x y) (n : ℕ) (hn : 24 ≤ n)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) : 0 < twoAtomRaw u (1+h) p d n σ x y := by
  rcases le_total (n*Real.arcosh (1+h)) 3 with h | h
  · exact twoAtomRaw_pos_small hb n hn h σ hσ
  · exact twoAtomRaw_pos_large hb n (by omega) h σ hσ

/-- Article: strict positivity of the actual normalized primal lag, not just its numerator. -/
theorem normalized_twoAtom_pos {h u p d : ℝ} {x y : Frequency}
    (hb : TailBounds h u p d x y) (n : ℕ) (hn : 24 ≤ n)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    0 < ((1-p)*actualRaw u (1+h) n σ x+p*actualRaw u (1+h) n σ y)/
      lagDenominator (1+h) n-σ*d := by
  have hd := lagDenominator_pos (by linarith [hb.h_pos] : (1 : ℝ) ≤ 1+h) n (by omega)
  have he : ((1-p)*actualRaw u (1+h) n σ x+p*actualRaw u (1+h) n σ y)/
      lagDenominator (1+h) n-σ*d=twoAtomRaw u (1+h) p d n σ x y/lagDenominator (1+h) n := by
    unfold twoAtomRaw
    field_simp [hd.ne']
  rw [he]
  exact div_pos (twoAtomRaw_pos_of_tailBounds hb n hn σ hσ) hd

end polyak.Boundary.P5
