import polyak.General.QuadraticScalar
import Mathlib.Topology.Order.LiminfLimsup

/-! Article: the actual from-rest exponential rate on a scalar quadratic.
The nth-root limsup is proved, including repeated, complex and zero roots. -/
noncomputable section
namespace polyak.General
open Filter
open scoped Topology

def quadraticScalarRoot (p β : ℝ) (n : ℕ) : ℝ :=
  |quadraticScalar p β n|^((n:ℝ)⁻¹)
def quadraticScalarRate (p β : ℝ) : ℝ := limsup (quadraticScalarRoot p β) atTop

theorem quadraticScalar_crude_bound (p β : ℝ) (n : ℕ) :
    |quadraticScalar p β n|≤(1+|p|+|β|)^n := by
  let K := 1+|p|+|β|
  have hK : 1≤K := by dsimp [K]; linarith [abs_nonneg p,abs_nonneg β]
  have hcoef : |p| *K+|β|≤K^2 := by
    dsimp [K]
    nlinarith [abs_nonneg p,abs_nonneg β,mul_nonneg (abs_nonneg p) (abs_nonneg β)]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa only [quadraticScalar_one,pow_one] using
      (abs_sub p β).trans (by linarith)
  | more n ih ih1 =>
    rw [quadraticScalar_recurrence]
    calc
      _≤|p*quadraticScalar p β (n+1)|+|β*quadraticScalar p β n| := abs_sub _ _
      _≤|p| *K^(n+1)+|β| *K^n := by rw [abs_mul,abs_mul]; gcongr
      _=(|p| *K+|β|)*K^n := by rw [pow_succ]; ring
      _≤K^2*K^n := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by linarith) _)
      _=K^(n+2) := by rw [pow_add]; ring

theorem quadraticScalarRoot_nonneg (p β : ℝ) (n : ℕ) : 0≤quadraticScalarRoot p β n :=
  Real.rpow_nonneg (abs_nonneg _) _
theorem quadraticScalarRoot_bound (p β : ℝ) (n : ℕ) :
    quadraticScalarRoot p β n≤1+|p|+|β| := by
  by_cases hn : n=0
  · simp only [quadraticScalarRoot,hn,Nat.cast_zero,inv_zero,Real.rpow_zero]
    linarith [abs_nonneg p,abs_nonneg β]
  · apply (Real.rpow_le_rpow (abs_nonneg _) (quadraticScalar_crude_bound p β n)
      (by positivity : 0≤(n:ℝ)⁻¹)).trans_eq
    exact Real.pow_rpow_inv_natCast (by positivity) hn

theorem quadraticScalarRoot_isBounded (p β : ℝ) :
    atTop.IsBoundedUnder (·≤·) (quadraticScalarRoot p β) :=
  isBoundedUnder_of ⟨_,quadraticScalarRoot_bound p β⟩
theorem quadraticScalarRate_nonneg (p β : ℝ) : 0≤quadraticScalarRate p β := by
  apply le_limsup_of_le (quadraticScalarRoot_isBounded p β)
  intro b hb
  obtain ⟨n,hn⟩ := hb.exists
  exact (quadraticScalarRoot_nonneg p β n).trans hn

theorem quadraticScalar_scaled_tendsto {p β R : ℝ} (hβ : 0≤β)
    (hR : rootRadius p β<R) :
    Tendsto (fun n => (quadraticScalar p β n:ℂ)/(R:ℂ)^n) atTop (𝓝 0) := by
  have hR0 : 0<R := (rootRadius_nonneg _ _).trans_lt hR
  have hRc : (R:ℂ)≠0 := by exact_mod_cast ne_of_gt hR0
  obtain ⟨r,hr⟩ := Dynamics.exists_complex_quadratic_root p β
  let s : ℂ := (p:ℂ)-r
  have hrs : r+s=(p:ℂ) := by dsimp [s]; ring
  have hprod : r*s=(β:ℂ) := by dsimp [s]; linear_combination -hr
  have hs : s^2-(p:ℂ)*s+(β:ℂ)=0 := by dsimp [s]; linear_combination hr
  have hsmall {z : ℂ} (hz : z^2-(p:ℂ)*z+(β:ℂ)=0) : ‖z/(R:ℂ)‖<1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0,div_lt_one hR0]
    exact (root_norm_le hβ hz).trans_lt hR
  apply Dynamics.recurrence_tendsto_zero_of_roots _ (r/(R:ℂ)) (s/(R:ℂ)) (hsmall hr) (hsmall hs)
  intro n
  have hcoef : (r/(R:ℂ))*(s/(R:ℂ))=(β:ℂ)/(R:ℂ)^2 := by
    rw [div_mul_div_comm,hprod,pow_two]
  rw [← add_div,hrs,hcoef]
  have hrec : (quadraticScalar p β (n+2):ℂ)=
      (p:ℂ)*(quadraticScalar p β (n+1):ℂ)-(β:ℂ)*(quadraticScalar p β n:ℂ) := by
    exact_mod_cast quadraticScalar_recurrence p β n
  rw [pow_add,pow_add]
  norm_num only [pow_one]
  field_simp
  linear_combination hrec

theorem quadraticScalar_eventually_le_pow {p β R : ℝ} (hβ : 0≤β)
    (hR : rootRadius p β<R) : ∀ᶠ n : ℕ in atTop,|quadraticScalar p β n|≤R^n := by
  have hR0 : 0<R := (rootRadius_nonneg _ _).trans_lt hR
  have ht := (quadraticScalar_scaled_tendsto hβ hR).norm
  simp only [norm_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0] at hn
  exact ((div_lt_one (pow_pos hR0 _)).1 hn).le

theorem quadraticScalarRate_le_of_gt_radius {p β R : ℝ} (hβ : 0≤β)
    (hR : rootRadius p β<R) : quadraticScalarRate p β≤R := by
  have hR0 : 0<R := (rootRadius_nonneg _ _).trans_lt hR
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (quadraticScalarRoot_nonneg p β))
  filter_upwards [quadraticScalar_eventually_le_pow hβ hR,eventually_gt_atTop 0] with n hn hn0
  apply (Real.rpow_le_rpow (abs_nonneg _) hn (by positivity : 0≤(n:ℝ)⁻¹)).trans_eq
  exact Real.pow_rpow_inv_natCast hR0.le (by omega)

theorem quadraticScalarRate_le_rootRadius {p β : ℝ} (hβ : 0≤β) :
    quadraticScalarRate p β≤rootRadius p β := by
  by_contra h
  obtain ⟨R,hR,hRate⟩ := exists_between (lt_of_not_ge h)
  exact (not_lt_of_ge (quadraticScalarRate_le_of_gt_radius hβ hR)) hRate

end polyak.General
