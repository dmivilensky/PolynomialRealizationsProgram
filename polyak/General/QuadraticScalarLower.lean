import polyak.General.QuadraticScalarLimit

/-! The from-rest impulse cannot cancel a nonzero characteristic root
at any positive curvature. This proves the literal scalar nth-root limsup. -/
noncomputable section
namespace polyak.General
open Filter
open scoped Topology

theorem quadraticScalar_no_smaller_envelope {p β R : ℝ} (hβ : 0≤β)
    (hcurv : 0<1+β-p) (hR0 : 0≤R) (hR : R<rootRadius p β)
    {C : ℝ} (_hC : 0≤C) :
    ¬ ∀ᶠ n : ℕ in atTop,|quadraticScalar p β n|≤C*R^n := by
  intro hEnv
  obtain ⟨r,hr,hrr⟩ := (rootRadius_isGreatest (p:=p) hβ).1
  have hrpos : 0<rootRadius p β := lt_of_le_of_lt hR0 hR
  have hrnorm : 0<‖r‖ := by simpa only [hrr] using hrpos
  have hr0 : r≠0 := norm_pos_iff.mp hrnorm
  have hdiff := quadratic_root_ne_beta hβ hcurv hr hr0
  have hdiffnorm : 0<‖r-(β:ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdiff)
  let s : ℂ := (p:ℂ)-r
  have hp : r+s=(p:ℂ) := by dsimp [s]; ring
  have hb : r*s=(β:ℂ) := by dsimp [s]; linear_combination -hr
  rcases eventually_atTop.mp hEnv with ⟨N,hN⟩
  have hbound (n : ℕ) (hn : N≤n) :
      ‖r-(β:ℂ)‖*(rootRadius p β)^n≤C*(R+‖s‖)*R^n := by
    have hdef := quadraticScalar_defect hp hb n
    have he : ‖r-(β:ℂ)‖*(rootRadius p β)^n=
        ‖(quadraticScalar p β (n+1):ℂ)-s*(quadraticScalar p β n:ℂ)‖ := by
      rw [hdef,norm_mul,norm_pow,← hrr]
    rw [he]
    calc
      _≤‖(quadraticScalar p β (n+1):ℂ)‖+‖s*(quadraticScalar p β n:ℂ)‖ := norm_sub_le _ _
      _=|quadraticScalar p β (n+1)|+‖s‖*|quadraticScalar p β n| := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs]
      _≤C*R^(n+1)+‖s‖*(C*R^n) := add_le_add (hN (n+1) (by omega))
        (mul_le_mul_of_nonneg_left (hN n hn) (norm_nonneg _))
      _=C*(R+‖s‖)*R^n := by rw [pow_succ]; ring
  have hratio0 : 0≤R/rootRadius p β := div_nonneg hR0 hrpos.le
  have hratio1 : R/rootRadius p β<1 := (div_lt_one hrpos).mpr hR
  have hlim : Tendsto (fun n : ℕ => C*(R+‖s‖)*(R/rootRadius p β)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).const_mul (C*(R+‖s‖))
  have hcmp : ∀ᶠ n : ℕ in atTop,‖r-(β:ℂ)‖≤C*(R+‖s‖)*(R/rootRadius p β)^n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    calc
      ‖r-(β:ℂ)‖≤C*(R+‖s‖)*R^n/(rootRadius p β)^n :=
        (le_div_iff₀ (pow_pos hrpos n)).mpr (hbound n hn)
      _=C*(R+‖s‖)*(R/rootRadius p β)^n := by rw [div_pow]; ring
  have hzero : ‖r-(β:ℂ)‖≤0 := ge_of_tendsto hlim hcmp
  linarith

theorem rootRadius_le_quadraticScalarRate {p β : ℝ} (hβ : 0≤β)
    (hcurv : 0<1+β-p) : rootRadius p β≤quadraticScalarRate p β := by
  by_contra h
  have hlt : quadraticScalarRate p β<rootRadius p β := lt_of_not_ge h
  obtain ⟨R,hRate,hR⟩ := exists_between hlt
  have hR0 : 0<R := lt_of_le_of_lt (quadraticScalarRate_nonneg p β) hRate
  have he : ∀ᶠ n : ℕ in atTop,quadraticScalarRoot p β n<R :=
    eventually_lt_of_limsup_lt hRate (quadraticScalarRoot_isBounded p β)
  have hEnv : ∀ᶠ n : ℕ in atTop,|quadraticScalar p β n|≤(1:ℝ)*R^n := by
    filter_upwards [he,eventually_gt_atTop 0] with n hn hn0
    rw [one_mul]
    have hneq : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
    have hpow := Real.rpow_le_rpow (quadraticScalarRoot_nonneg p β n) hn.le
      (show 0≤(n:ℝ) by positivity)
    have hex : (|quadraticScalar p β n|^((n:ℝ)⁻¹))^(n:ℝ)=|quadraticScalar p β n| := by
      rw [← Real.rpow_mul (abs_nonneg _),inv_mul_cancel₀ hneq,Real.rpow_one]
    simpa only [quadraticScalarRoot,hex,Real.rpow_natCast] using hpow
  exact quadraticScalar_no_smaller_envelope hβ hcurv hR0.le hR (by norm_num) hEnv

theorem quadraticScalarRate_eq_rootRadius {p β : ℝ} (hβ : 0≤β)
    (hcurv : 0<1+β-p) : quadraticScalarRate p β=rootRadius p β :=
  le_antisymm (quadraticScalarRate_le_rootRadius hβ) (rootRadius_le_quadraticScalarRate hβ hcurv)

theorem quadraticScalar_actual_limsup {α β lam : ℝ} (hαlam : 0<α*lam) (hβ : 0≤β) :
    limsup (fun n : ℕ => |Dynamics.iterate (fun x : ℝ => lam*x) α β 1 n|^((n:ℝ)⁻¹)) atTop=
      rootRadius (1+β-α*lam) β := by
  simp_rw [quadraticScalar_iterate]
  exact quadraticScalarRate_eq_rootRadius hβ (by linarith)

end polyak.General
