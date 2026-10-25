import polyak.Realization.ExplicitSpiral.Oscillation
import polyak.Realization.ExplicitSpiral.Star

/-!
Article: all exceptional interpolation pairs of the fixed Y=2 spiral.
Use: finite exact source signs plus analytic phase and tail bounds cover all times.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation

/-- Article: the exceptional pair slack with its actual scalar response. -/
def initializedPairSlack (r q δ : ℝ) (k : ℕ) : ℝ :=
  pairRadius (multiplier (radialWave r) q) (defect (radialWave r) q) (radialWave r^k)+
    δ*pairDiscrepancy (multiplier (radialWave r) q) (defect (radialWave r) q)
      (radialWave r^k) (Source.valueConstant r q)+(1-response 0 (q^2) k)^2

/-- Article: each finite source slack is precisely the actual initialized slack. -/
theorem initializedPairSlack_eq_source {r q : ℝ} (hr : 0<r) (hq : 0<q) (δ : ℝ) (k : ℕ) :
    initializedPairSlack r q δ k=Source.pairSlack r q δ k := by
  obtain ⟨_,hn,hz⟩ := radial_wave_coordinates hr
  unfold initializedPairSlack Source.pairSlack
  rw [pairRadius_eq_source hr hq hn hz,pairDiscrepancy_eq_source hr hq hn hz,response_source]

/-- Article: all stationary initial-pair signs already follow from spiral feasibility. -/
theorem stationary_initial_pair_nonneg {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0) (δ : ℝ) (hδ : δ=1 ∨ δ= -1) (k : ℕ) :
    0≤pairRadius (multiplier (radialWave r) q) 0 (radialWave r^k)+
      δ*pairDiscrepancy (multiplier (radialWave r) q) 0 (radialWave r^k)
        (Source.valueConstant r q) := by
  have hh := stationary_tableFeasible hr hq hF (some 0) (some k)
  have hs := (multiplier_defect_coordinates hr hq
    (radial_wave_coordinates hr).2.1 (radial_wave_coordinates hr).2.2).1
  have hb : Source.valueConstant r q=(physicalValueConstant r+2*(multiplier (radialWave r) q).re)/4 :=
    by rw [hs]; rfl
  have he : |pairDiscrepancy (multiplier (radialWave r) q) 0 (radialWave r^k)
      (Source.valueConstant r q)|≤pairRadius (multiplier (radialWave r) q) 0 (radialWave r^k) := by
    simpa only [datumT,datumR,modePosition,modeGradient,modeValue,pow_zero,mul_one,
      pairRadius,pairDiscrepancy,add_zero,hb,Complex.sq_norm,Complex.normSq_one,mul_one] using hh
  obtain ⟨hl,hu⟩ := abs_le.mp he
  rcases hδ with rfl | rfl <;> nlinarith

/-- Article: q≤1/5 is controlled uniformly by the explicit 99/100 scalar reserve. -/
theorem small_initialized_pair_pos {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq5 : q≤1/5)
    (hF : Spiral.spiralPolynomial r q=0) (δ : ℝ) (hδ : δ=1 ∨ δ= -1)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q δ k := by
  obtain ⟨hn,hn2,hz⟩ := radial_wave_coordinates hr
  have hrhalf := root_lt_half hr hq hq5 hF
  have hp : ‖radialWave r^k‖≤1/2 := by
    rw [norm_pow,hn]
    have hh := pow_le_pow_of_le_one hr.le (show r≤1 by linarith) hk
    simp only [pow_one] at hh
    exact hh.trans hrhalf.le
  exact small_pair_positive hq.le hq5 _ _ _ _ _ k hk
    (norm_multiplier_le_one hr hq hn2 hz hF) (small_norm_defect hr hq hq5 hF) hp
    (by rcases hδ with rfl | rfl <;> norm_num)
    (stationary_initial_pair_nonneg hr hq hF δ hδ k)

/-- Article: both quadratic coefficients are strictly positive on the full physical domain. -/
theorem source_quadratic_pos {r : ℝ} (hr : 0<r) (δ : ℝ) (hδ : δ=1 ∨ δ= -1) :
    0<Source.quadratic r δ := by
  have hg := source_gap_pos hr
  have hG : 0<Source.hyperbolic r := by unfold Source.hyperbolic; positivity
  rcases hδ with rfl | rfl <;> norm_num [Source.quadratic] <;> positivity

/-- Article: the disk-region two exact signs control every positive index. -/
theorem disk_initialized_pair_pos {r q δ : ℝ} (hr : 0<r) (hr1 : r≤1)
    (hq : 0<q) (hq1 : q<1) (hF : Spiral.spiralPolynomial r q=0)
    (hδ : δ=1 ∨ δ= -1)
    (hc : 0<Source.constant r q δ+Source.reserve q)
    (hnorm : 0<(Source.constant r q δ+Source.reserve q)^2-Source.betaNorm r q δ)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q δ k := by
  obtain ⟨hn,hn2,hz⟩ := radial_wave_coordinates hr
  let β := oscillationCoefficient r q (radialWave r) δ
  have hβ : ‖β‖^2=Source.betaNorm r q δ := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_oscillationCoefficient hn2 hz δ
  have hp : 0<Source.quadratic r δ*(r^k)^2+(β*radialWave r^k).re+
      (Source.constant r q δ+Source.reserve q) := by
    apply disk_slack_pos (source_quadratic_pos hr δ hδ).le (norm_nonneg β) hc
      (by rwa [hβ]) (by positivity) (pow_le_one₀ hr.le hr1)
    simpa only [norm_pow,hn] using oscillation_lower β (radialWave r^k)
  have he := actual_pair_normal_form hr hq hn2 hz hF δ (radialWave r^k)
  have hpow := normSq_power hn2 k
  have hres := response_reserve hq.le hq1.le k hk
  unfold initializedPairSlack
  rw [he,hpow,show r^(2*k)=(r^k)^2 by rw [← pow_mul]; congr 1; omega]
  change 0<Source.quadratic r δ*(r^k)^2+(β*radialWave r^k).re+Source.constant r q δ+
    (1-response 0 (q^2) k)^2
  linarith

/-- Article: the three residue quadratics control all times near the unit circle. -/
theorem phase_initialized_pair_pos {r q δ : ℝ} (hr : 1≤r)
    (hq : 0<q) (hq1 : q<1) (hF : Spiral.spiralPolynomial r q=0)
    (hbeta : 0<1-Source.betaNorm r q δ)
    (ha : 0<Source.quadratic r δ-phaseBudget r)
    (hquad : ∀ a : ℕ,a<3 →
      0<(Source.quadratic r δ-phaseBudget r)+(Source.residue r q δ a+phaseBudget r)+
        (Source.constant r q δ+Source.reserve q) ∧
      (0<2*(Source.quadratic r δ-phaseBudget r)+(Source.residue r q δ a+phaseBudget r) ∨
       0<4*(Source.quadratic r δ-phaseBudget r)*(Source.constant r q δ+Source.reserve q)-
         (Source.residue r q δ a+phaseBudget r)^2))
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q δ k := by
  have hr0 : 0<r := by linarith
  obtain ⟨_,hn2,hz⟩ := radial_wave_coordinates hr0
  let β := oscillationCoefficient r q (radialWave r) δ
  let X := r^k
  let a := k%3
  let j := k/3
  have hnat : 3*j+a=k := by dsimp [j,a]; omega
  have hX : 1≤X := one_le_pow₀ hr
  have hX0 : 0≤X := by linarith
  have hβsq : ‖β‖^2=Source.betaNorm r q δ := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_oscillationCoefficient hn2 hz δ
  have hβ : ‖β‖≤1 := by nlinarith [norm_nonneg β,hbeta]
  have hε : 0≤phaseBudget r := by
    unfold phaseBudget
    have hsq : 0≤r^2-1 := by nlinarith
    positivity
  have hD : 0≤phaseBudget r*Real.log X := mul_nonneg hε (Real.log_nonneg hX)
  have hphase := unitPhase_residue hr j a
  rw [hnat] at hphase
  have hos := residue_oscillation_lower hβ hX0 hD hphase
  rw [← source_residue_eq hr0 δ a] at hos
  have hosc : (β*radialWave r^k).re=
      X*(β*unitPhase ((k : ℝ)*Real.arccos (radialCosine r))).re := by
    rw [radial_wave_pow hr0]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero]
    dsimp [X]
    ring
  have hlog := Real.log_le_sub_one_of_pos (show 0<X by linarith)
  have hlogloss : X*(phaseBudget r*Real.log X)≤phaseBudget r*X*(X-1) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (mul_nonneg hε hX0)]
  obtain ⟨h1,hd⟩ := hquad a (Nat.mod_lt _ (by norm_num))
  have hp : 0<(Source.quadratic r δ-phaseBudget r)*X^2+
      (Source.residue r q δ a+phaseBudget r)*X+(Source.constant r q δ+Source.reserve q) :=
    hd.elim (fun h => quadratic_pos_of_derivative ha h1 h.le hX)
      (fun h => quadratic_pos_of_discriminant ha h)
  have he := actual_pair_normal_form hr0 hq hn2 hz hF δ (radialWave r^k)
  have hres := response_reserve hq.le hq1.le k hk
  have hpow : Complex.normSq (radialWave r^k)=X^2 := by
    rw [normSq_power hn2,show r^(2*k)=(r^k)^2 by rw [← pow_mul]; congr 1; omega]
  unfold initializedPairSlack
  rw [he,hpow]
  change 0<Source.quadratic r δ*X^2+(β*radialWave r^k).re+Source.constant r q δ+
    (1-response 0 (q^2) k)^2
  rw [hosc]
  nlinarith

/-- Article: the large-growth three source signs prove every lag from ten onward. -/
theorem tail_initialized_pair_pos {r q δ : ℝ} (hr : 1≤r)
    (hq : 0<q) (hq1 : q<1) (hF : Spiral.spiralPolynomial r q=0)
    (hδ : δ=1 ∨ δ= -1)
    (hd : 0<4*(Source.quadratic r δ)^2*r^20-Source.betaNorm r q δ)
    (hc : 0<Source.quadratic r δ*r^20+Source.constant r q δ+Source.reserve q)
    (hcb : 0<(Source.quadratic r δ*r^20+Source.constant r q δ+Source.reserve q)^2-
      Source.betaNorm r q δ*r^20) (k : ℕ) (hk : 10≤k) :
    0 < initializedPairSlack r q δ k := by
  have hr0 : 0<r := by linarith
  obtain ⟨hn,hn2,hz⟩ := radial_wave_coordinates hr0
  let β := oscillationCoefficient r q (radialWave r) δ
  have hβsq : ‖β‖^2=Source.betaNorm r q δ := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_oscillationCoefficient hn2 hz δ
  have hten : (r^10)^2=r^20 := by rw [← pow_mul]
  have hp : 0<Source.quadratic r δ*(r^k)^2+(β*radialWave r^k).re+
      (Source.constant r q δ+Source.reserve q) := by
    apply tail_slack_pos (source_quadratic_pos hr0 δ hδ) (norm_nonneg β)
      (by positivity : 0≤r^10) (pow_le_pow_right₀ hr hk)
    · simpa only [hten,hβsq] using hd
    · simpa only [hten,add_assoc] using hc
    · simpa only [hten,hβsq,add_assoc] using hcb
    · simpa only [norm_pow,hn] using oscillation_lower β (radialWave r^k)
  have he := actual_pair_normal_form hr0 hq hn2 hz hF δ (radialWave r^k)
  have hres := response_reserve hq.le hq1.le k (by omega)
  unfold initializedPairSlack
  rw [he,normSq_power hn2,show r^(2*k)=(r^k)^2 by rw [← pow_mul]; congr 1; omega]
  change 0<Source.quadratic r δ*(r^k)^2+(β*radialWave r^k).re+Source.constant r q δ+
    (1-response 0 (q^2) k)^2
  linarith

end
end polyak.Realization.ExplicitSpiral
