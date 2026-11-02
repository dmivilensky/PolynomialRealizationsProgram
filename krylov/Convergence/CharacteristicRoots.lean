import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
Article: main_krylov, lem:rorder2 and Table s7-orders.
Use: construct the actual unique positive characteristic roots of the
secant recurrences, including the one-dimensional corrected order two.
Source: the elementary characteristic-equation argument of Ortega and
Rheinboldt (1970), using the intermediate value theorem and strict powers.
-/
namespace krylov.Convergence
noncomputable section
open Set

/-- A polynomial form of the characteristic equation, with no division.
Article: main_krylov, lem:rorder2(a). -/
def characteristicPolynomial (p q : ℕ) (t : ℝ) : ℝ :=
  t^(p-q)*(t^(q+1)-1)

/-- The characteristic polynomial increases strictly above one.
Article: main_krylov, lem:rorder2. -/
theorem characteristicPolynomial_strictMono (p q : ℕ) :
    StrictMonoOn (characteristicPolynomial p q) (Ici 1) := by
  intro x hx y hy hxy
  have hx₀ : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hy₀ : 0<y := lt_of_lt_of_le zero_lt_one hy
  have hb : x^(q+1)<y^(q+1) := pow_lt_pow_left₀ hxy hx₀.le (by omega)
  have ha : x^(p-q)≤y^(p-q) := pow_le_pow_left₀ hx₀.le hxy.le _
  have hg : 0≤y^(q+1)-1 := sub_nonneg.mpr (one_le_pow₀ hy)
  exact (mul_lt_mul_of_pos_left (sub_lt_sub_right hb 1) (pow_pos hx₀ _)).trans_le
    (mul_le_mul_of_nonneg_right ha hg)

/-- The genuine characteristic root exists in (1,2].
Article: main_krylov, lem:rorder2. -/
theorem exists_characteristicRoot (p q : ℕ) :
    ∃ t : ℝ, 1<t ∧ t≤2 ∧ characteristicPolynomial p q t=1 := by
  have hc : ContinuousOn (characteristicPolynomial p q) (Icc 1 2) := by
    unfold characteristicPolynomial
    fun_prop
  have htwo : (2 : ℝ)≤2^(q+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 1≤q+1)
  have hb : 1≤characteristicPolynomial p q 2 := by
    have ha : (1:ℝ)≤2^(p-q) := one_le_pow₀ (by norm_num)
    unfold characteristicPolynomial
    nlinarith only [ha,htwo]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (1:ℝ)≤2) hc
    (show (1:ℝ)∈Icc (characteristicPolynomial p q 1) (characteristicPolynomial p q 2) from
      ⟨by simp [characteristicPolynomial],hb⟩)
  refine ⟨t,?_,ht.2,he⟩
  by_contra hn
  have hz : t=1 := le_antisymm (not_lt.mp hn) ht.1
  simp only [hz,characteristicPolynomial,one_pow,sub_self,mul_zero] at he
  norm_num at he

/-- The actual unique root, selected from its proved real existence.
Article: main_krylov, lem:rorder2. -/
def secantRoot (p q : ℕ) : ℝ := (exists_characteristicRoot p q).choose

theorem secantRoot_gt_one (p q : ℕ) : 1<secantRoot p q :=
  (exists_characteristicRoot p q).choose_spec.1

theorem secantRoot_le_two (p q : ℕ) : secantRoot p q≤2 :=
  (exists_characteristicRoot p q).choose_spec.2.1

theorem secantRoot_polynomial (p q : ℕ) : characteristicPolynomial p q (secantRoot p q)=1 :=
  (exists_characteristicRoot p q).choose_spec.2.2

/-- The printed characteristic equation, including the equal-lag order-two case.
Article: main_krylov, lem:rorder2(a). -/
theorem secantRoot_equation (p q : ℕ) (hq : q≤p) :
    secantRoot p q^(p+1)=secantRoot p q^(p-q)+1 := by
  have h := secantRoot_polynomial p q
  unfold characteristicPolynomial at h
  rw [show p+1=(p-q)+(q+1) by omega,pow_add]
  nlinarith only [h]

/-- Among all positive reals the printed characteristic equation has
exactly the constructed root. Article: main_krylov, lem:rorder2(a). -/
theorem secantRoot_unique (p q : ℕ) (hq : q≤p) {t : ℝ} (ht : 0<t)
    (he : t^(p+1)=t^(p-q)+1) : t=secantRoot p q := by
  have hpoly : characteristicPolynomial p q t=1 := by
    unfold characteristicPolynomial
    rw [show p+1=(p-q)+(q+1) by omega,pow_add] at he
    nlinarith only [he]
  have ht₁ : 1<t := by
    by_contra hn
    have hh : t^(q+1)≤1 := pow_le_one₀ ht.le (not_lt.mp hn)
    have ha : 0≤t^(p-q) := pow_nonneg ht.le _
    unfold characteristicPolynomial at hpoly
    nlinarith only [hh,ha,hpoly]
  exact (characteristicPolynomial_strictMono p q).injOn ht₁.le (secantRoot_gt_one p q).le
    (hpoly.trans (secantRoot_polynomial p q).symm)

/-- The article's one-gradient root t^m=t^(m-1)+1.
Article: main_krylov, lem:rorder2 and Table s7-orders. -/
def oneGradientRoot (m : ℕ) : ℝ := secantRoot (m-1) 0

theorem oneGradientRoot_equation {m : ℕ} (hm : 0<m) :
    oneGradientRoot m^m=oneGradientRoot m^(m-1)+1 := by
  simpa only [oneGradientRoot,Nat.sub_zero,Nat.sub_add_cancel hm] using
    secantRoot_equation (m-1) 0 (Nat.zero_le _)

/-- Full conjugacy's characteristic root t^n=t+1.
Article: main_krylov, thm:G and Table s7-orders. -/
def fullConjugacyRoot (n : ℕ) : ℝ := secantRoot (n-1) (n-2)

theorem fullConjugacyRoot_equation {n : ℕ} (hn : 2≤n) :
    fullConjugacyRoot n^n=fullConjugacyRoot n+1 := by
  have hh := secantRoot_equation (n-1) (n-2) (by omega)
  simpa only [fullConjugacyRoot,show n-1+1=n by omega,show n-1-(n-2)=1 by omega,pow_one] using hh

end
end krylov.Convergence
