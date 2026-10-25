import polyak.General.Roots
import polyak.General.IQC.Fundamental
import polyak.Dynamics.QuadraticLimit

/-! Article: introduction and Part II §6.1, the actual rate on quadratics.
This is the genuine zero-momentum scalar executor, not a free-state root mode. -/
noncomputable section
namespace polyak.General
open IQC

def quadraticScalar (p β : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => p-β
  | n+2 => p*quadraticScalar p β (n+1)-β*quadraticScalar p β n

@[simp] theorem quadraticScalar_zero (p β : ℝ) : quadraticScalar p β 0=1 := rfl
@[simp] theorem quadraticScalar_one (p β : ℝ) : quadraticScalar p β 1=p-β := rfl
theorem quadraticScalar_recurrence (p β : ℝ) (n : ℕ) :
    quadraticScalar p β (n+2)=p*quadraticScalar p β (n+1)-β*quadraticScalar p β n := rfl

theorem quadraticScalar_iterate (α β lam : ℝ) (n : ℕ) :
    Dynamics.iterate (fun x : ℝ => lam*x) α β 1 n=quadraticScalar (1+β-α*lam) β n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more n ih ih1 =>
    rw [Dynamics.iterate_recurrence,quadraticScalar_recurrence,ih,ih1]
    simp only [smul_eq_mul]
    ring

theorem quadraticScalar_fundamental (p β : ℝ) (n : ℕ) :
    quadraticScalar p β (n+1)=fundamental p β (n+1)-β*fundamental p β n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fundamental]
  | one => simp [fundamental,quadraticScalar]; ring
  | more n ih ih1 =>
    rw [show n+2+1=(n+1)+2 by omega,quadraticScalar_recurrence,ih1,ih]
    simp only [fundamental]
    ring

theorem fundamental_rootRadius_bound {p β : ℝ} (hβ : 0≤β) (n : ℕ) :
    |fundamental p β n|≤((n:ℝ)+1)*(rootRadius p β)^n := by
  obtain ⟨r,hr⟩ := Dynamics.exists_complex_quadratic_root p β
  let s : ℂ := (p:ℂ)-r
  have hrs : r+s=(p:ℂ) := by dsimp [s]; ring
  have hprod : r*s=(β:ℂ) := by dsimp [s]; linear_combination -hr
  have hs : s^2-(p:ℂ)*s+(β:ℂ)=0 := by dsimp [s]; linear_combination hr
  have hR : max ‖r‖ ‖s‖≤rootRadius p β := max_le (root_norm_le hβ hr) (root_norm_le hβ hs)
  calc
    _=‖(fundamental p β n:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
    _=‖rootSum r s n‖ := by rw [fundamental_complex hrs hprod]
    _≤((n:ℝ)+1)*(max ‖r‖ ‖s‖)^n := rootSum_norm_le _ _ _
    _≤_ := by gcongr

theorem quadraticScalar_bound {p β : ℝ} (hβ : 0≤β) (n : ℕ) :
    |quadraticScalar p β (n+1)|≤((n:ℝ)+2)*(rootRadius p β)^(n+1)+
      |β| *((n:ℝ)+1)*(rootRadius p β)^n := by
  rw [quadraticScalar_fundamental]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have h1 := fundamental_rootRadius_bound (p:=p) hβ (n+1)
  have h0 := fundamental_rootRadius_bound (p:=p) hβ n
  simp only [Nat.cast_add,Nat.cast_one] at h1
  nlinarith [mul_nonneg (abs_nonneg β) (sub_nonneg.2 h0)]

theorem quadraticScalar_defect {p β : ℝ} {r s : ℂ}
    (hp : r+s=(p:ℂ)) (hβ : r*s=(β:ℂ)) (n : ℕ) :
    (quadraticScalar p β (n+1):ℂ)-s*(quadraticScalar p β n:ℂ)=
      (r-(β:ℂ))*r^n := by
  induction n with
  | zero => simp only [Nat.zero_add,quadraticScalar_one,quadraticScalar_zero,Complex.ofReal_sub,
      Complex.ofReal_one,mul_one,pow_zero]; linear_combination -hp
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,quadraticScalar_recurrence,
      Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_mul]
    have he : (p:ℂ)=(r+s) := hp.symm
    rw [he,pow_succ]
    linear_combination r*ih + (quadraticScalar p β n:ℂ)*hβ

theorem quadratic_root_ne_beta {p β : ℝ} (hβ : 0≤β) (hcurv : 0<1+β-p)
    {r : ℂ} (hr : r^2-(p:ℂ)*r+(β:ℂ)=0) (hr0 : r≠0) : r≠(β:ℂ) := by
  intro he
  rw [he] at hr
  have hb0 : β≠0 := by intro hb; apply hr0; simpa only [hb,Complex.ofReal_zero] using he
  have he' : β^2-p*β+β=0 := by exact_mod_cast hr
  nlinarith [mul_pos (lt_of_le_of_ne hβ (Ne.symm hb0)) hcurv]

end polyak.General
