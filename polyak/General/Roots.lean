import polyak.General.Parameters

/-! Article: the quadratic factors, damping curves and Appendix D lem:dominant.
The formula below is proved to be the maximum over actual complex roots. -/
namespace polyak.General
noncomputable section

def rootRadius (p β : ℝ) : ℝ :=
  if p^2 ≤ 4*β then Real.sqrt β else (|p|+Real.sqrt (p^2-4*β))/2

theorem rootRadius_nonneg (p β : ℝ) : 0 ≤ rootRadius p β := by
  unfold rootRadius; split <;> positivity

theorem rootRadius_eq_sqrt {p β : ℝ} (h : p^2 ≤ 4*β) :
    rootRadius p β = Real.sqrt β := by simp only [rootRadius, h, ↓reduceIte]

theorem rootRadius_zero_momentum (p : ℝ) : rootRadius p 0=|p| := by
  by_cases hp : p=0
  · simp [rootRadius,hp]
  · have hd : ¬p^2≤0 := by nlinarith [sq_pos_of_ne_zero hp]
    simp only [rootRadius,mul_zero,hd,↓reduceIte,sub_zero,Real.sqrt_sq_eq_abs]
    ring

theorem rootRadius_isGreatest {p β : ℝ} (hβ : 0 ≤ β) :
    IsGreatest {r : ℝ | ∃ z : ℂ, z^2-(p : ℂ)*z+(β : ℂ)=0 ∧ r=‖z‖}
      (rootRadius p β) := by
  by_cases hd : p^2 ≤ 4*β
  · rw [rootRadius_eq_sqrt hd]
    have hn {z : ℂ} (hz : z^2-(p : ℂ)*z+(β : ℂ)=0) : ‖z‖=Real.sqrt β := by
      have he := Dynamics.quadratic_root_norm_sq hd hz
      have hs := Real.sq_sqrt hβ
      nlinarith [norm_nonneg z, Real.sqrt_nonneg β]
    obtain ⟨z,hz⟩ := Dynamics.exists_complex_quadratic_root p β
    exact ⟨⟨z,hz,(hn hz).symm⟩, fun _ ⟨z,hz,hr⟩ => by rw [hr,hn hz]⟩
  · have hd0 : 0 < p^2-4*β := by linarith
    have hs := Real.sq_sqrt hd0.le
    have hs0 := Real.sqrt_nonneg (p^2-4*β)
    have hreal {z : ℂ} (hz : z^2-(p : ℂ)*z+(β : ℂ)=0) : z.im=0 := by
      have hre := congrArg Complex.re hz
      have him := congrArg Complex.im hz
      simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre
      simp only [pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at him
      by_contra hi
      have hh : 2*z.re-p=0 :=
        (mul_eq_zero.mp (show z.im*(2*z.re-p)=0 by nlinarith)).resolve_left hi
      nlinarith [sq_nonneg z.im]
    have hbound {z : ℂ} (hz : z^2-(p : ℂ)*z+(β : ℂ)=0) :
        ‖z‖ ≤ (|p|+Real.sqrt (p^2-4*β))/2 := by
      have hi := hreal hz
      have hre := congrArg Complex.re hz
      simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero, Complex.zero_re,
        hi, mul_zero] at hre
      have hh : |2*z.re-p| ≤ Real.sqrt (p^2-4*β) := by
        rw [abs_le]; constructor <;> nlinarith
      have hzreal : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hi]
      rw [hzreal,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_le] at hh ⊢
      constructor <;> linarith [le_abs_self p,neg_abs_le p]
    simp only [rootRadius, hd, ↓reduceIte]
    constructor
    · by_cases hp : 0 ≤ p
      · refine ⟨((p+Real.sqrt (p^2-4*β))/2 : ℝ),?_,?_⟩
        · have he : ((p+Real.sqrt (p^2-4*β))/2)^2-p*((p+Real.sqrt (p^2-4*β))/2)+β=0 := by nlinarith
          exact_mod_cast he
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg (by positivity)]
      · have hp : p < 0 := lt_of_not_ge hp
        refine ⟨((p-Real.sqrt (p^2-4*β))/2 : ℝ),?_,?_⟩
        · have he : ((p-Real.sqrt (p^2-4*β))/2)^2-p*((p-Real.sqrt (p^2-4*β))/2)+β=0 := by nlinarith
          exact_mod_cast he
        · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg hp,abs_of_nonpos (by linarith)]
          ring
    · exact fun _ ⟨z,hz,hr⟩ => by rw [hr]; exact hbound hz

theorem root_norm_le {p β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : z^2-(p : ℂ)*z+(β : ℂ)=0) : ‖z‖ ≤ rootRadius p β :=
  (rootRadius_isGreatest hβ).2 ⟨z,hz,rfl⟩

theorem rootRadius_lt_one {p β : ℝ} (hβ : 0 ≤ β) (hβ1 : β<1)
    (hp : |p|<1+β) : rootRadius p β<1 := by
  obtain ⟨z,hz,hr⟩ := (rootRadius_isGreatest (p:=p) hβ).1
  rw [hr]
  exact Dynamics.quadratic_root_norm_lt_one hβ hβ1 hp hz

theorem sqrt_le_rootRadius {p β : ℝ} (hβ : 0 ≤ β) : Real.sqrt β ≤ rootRadius p β := by
  by_cases hd : p^2 ≤ 4*β
  · rw [rootRadius_eq_sqrt hd]
  · have hs := Real.sq_sqrt hβ
    have hp := abs_nonneg p
    have hpp : p^2=|p|^2 := (sq_abs p).symm
    have hb := Real.sqrt_nonneg β
    have hlt : 2*Real.sqrt β < |p| := by nlinarith
    simp only [rootRadius,hd,↓reduceIte]
    linarith [Real.sqrt_nonneg (p^2-4*β)]

theorem rootRadius_eq_sqrt_iff {p β : ℝ} (hβ : 0 ≤ β) :
    rootRadius p β=Real.sqrt β ↔ p^2≤4*β := by
  constructor
  · intro h
    by_contra hd
    have hs := Real.sq_sqrt hβ
    have hp := abs_nonneg p
    have hpp : p^2=|p|^2 := (sq_abs p).symm
    have hb := Real.sqrt_nonneg β
    have hlt : 2*Real.sqrt β < |p| := by nlinarith
    simp only [rootRadius,hd,↓reduceIte] at h
    linarith [Real.sqrt_nonneg (p^2-4*β)]
  · exact rootRadius_eq_sqrt

theorem rootRadius_strict_of_abs_lt {p p' β : ℝ} (hp : |p| < |p'|)
    (hd : 4*β < p'^2) : rootRadius p β < rootRadius p' β := by
  by_cases h : p^2 ≤ 4*β
  · rw [rootRadius_eq_sqrt h]
    have hβ : 0 ≤ β := by nlinarith [sq_nonneg p]
    have hs := Real.sq_sqrt hβ
    have hpp := sq_abs p'
    have hlt : 2*Real.sqrt β < |p'| := by
      nlinarith [abs_nonneg p',Real.sqrt_nonneg β]
    simp only [rootRadius,show ¬p'^2≤4*β from not_le.mpr hd,↓reduceIte]
    linarith [Real.sqrt_nonneg (p'^2-4*β)]
  · have hsq : p^2<p'^2 := by nlinarith [sq_abs p,sq_abs p',abs_nonneg p]
    have hsqrt := Real.sqrt_le_sqrt (show p^2-4*β ≤ p'^2-4*β by linarith)
    simp only [rootRadius,h,show ¬p'^2≤4*β from not_le.mpr hd,↓reduceIte]
    linarith

theorem rootRadius_mono_abs {p p' β : ℝ} (hp : |p| ≤ |p'|) :
    rootRadius p β ≤ rootRadius p' β := by
  by_cases hd : p'^2≤4*β
  · have h : p^2≤4*β := by nlinarith [sq_abs p,sq_abs p',abs_nonneg p]
    rw [rootRadius_eq_sqrt h,rootRadius_eq_sqrt hd]
  · rcases hp.eq_or_lt with h|h
    · have hsq : p^2=p'^2 := by rw [← sq_abs p, h, sq_abs p']
      simp only [rootRadius,h,hsq,le_refl]
    · exact (rootRadius_strict_of_abs_lt h (lt_of_not_ge hd)).le

namespace Tuning

def rhoA (q : Tuning) : ℝ := rootRadius (1+q.beta-q.x) q.beta
def rhoB (q : Tuning) : ℝ := rootRadius (1+q.beta-q.y) q.beta
def rhoQ (q : Tuning) : ℝ := max q.rhoA q.rhoB
def r0 (q : Tuning) : ℝ := rootRadius q.A q.beta

theorem r0_lt_one (q : Tuning) : q.r0<1 :=
  rootRadius_lt_one q.beta_nonneg q.beta_lt_one
    (lt_of_le_of_lt (by linarith [q.B_pos] : |q.A| ≤ |q.A|+q.B) q.abs_A_add_B_lt)

theorem scaled_root_stable (q : Tuning) {r : ℝ} (hr : q.r0<r) {z : ℂ}
    (hz : z^2-(q.A : ℂ)*z+(q.beta : ℂ)=0) : ‖z/(r : ℂ)‖<1 := by
  have hr0 : 0<r := lt_of_le_of_lt (rootRadius_nonneg _ _) hr
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,div_lt_one hr0]
  exact lt_of_le_of_lt (root_norm_le q.beta_nonneg hz) hr

theorem rhoQ_lt_one (q : Tuning) : q.rhoQ<1 := by
  apply max_lt
  · obtain ⟨z,hz,he⟩ := (rootRadius_isGreatest (p:=1+q.beta-q.x) q.beta_nonneg).1
    change q.rhoA<1
    dsimp [rhoA]; rw [he]
    exact q.a_root_stable hz
  · obtain ⟨z,hz,he⟩ := (rootRadius_isGreatest (p:=1+q.beta-q.y) q.beta_nonneg).1
    change q.rhoB<1
    dsimp [rhoB]; rw [he]
    exact q.b_root_stable hz

theorem quadraticRate_eq (q : Tuning) :
    Dynamics.quadraticRate q.x q.y 1 q.beta=q.rhoQ := by
  have hquad : 1*q.y<2*(1+q.beta) := by simpa using q.y_lt
  apply IsGreatest.unique (Dynamics.quadraticRate_isGreatest q.x_pos q.x_lt_y
    (by norm_num) q.beta_nonneg q.beta_lt_one hquad)
  constructor
  · rcases le_total q.rhoA q.rhoB with h|h
    · obtain ⟨z,hz,he⟩ := (rootRadius_isGreatest (p:=1+q.beta-q.y) q.beta_nonneg).1
      exact ⟨q.y,⟨q.x_lt_y.le,le_rfl⟩,z,by simpa using hz,by change max q.rhoA q.rhoB=‖z‖; rw [max_eq_right h]; exact he⟩
    · obtain ⟨z,hz,he⟩ := (rootRadius_isGreatest (p:=1+q.beta-q.x) q.beta_nonneg).1
      exact ⟨q.x,⟨le_rfl,q.x_lt_y.le⟩,z,by simpa using hz,by change max q.rhoA q.rhoB=‖z‖; rw [max_eq_left h]; exact he⟩
  · rintro r ⟨lam,hlam,z,hz,rfl⟩
    have hp : |1+q.beta-lam| ≤ max |1+q.beta-q.x| |1+q.beta-q.y| := by
      rw [abs_le]
      constructor
      · have h := le_max_right |1+q.beta-q.x| |1+q.beta-q.y|
        linarith [neg_abs_le (1+q.beta-q.y),hlam.2]
      · have h := le_max_left |1+q.beta-q.x| |1+q.beta-q.y|
        linarith [le_abs_self (1+q.beta-q.x),hlam.1]
    have hz' : z^2-((1+q.beta-lam : ℝ):ℂ)*z+(q.beta:ℂ)=0 := by simpa using hz
    apply (root_norm_le q.beta_nonneg hz').trans
    rcases le_total |1+q.beta-q.x| |1+q.beta-q.y| with h|h
    · rw [max_eq_right h] at hp
      exact (rootRadius_mono_abs hp).trans (le_max_right _ _)
    · rw [max_eq_left h] at hp
      exact (rootRadius_mono_abs hp).trans (le_max_left _ _)

end Tuning

end
end polyak.General
