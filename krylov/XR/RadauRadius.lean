import krylov.XR.RadauRawSource

/-!
Article: main_krylov, apG:radau-adequate, uniform small-error radius.
Use: choose one positive secant-error tolerance for every current memory
length at most n; no realized trajectory enters this choice.
Source: the explicit primitive augmented-frame and strict spectral margins.
-/
namespace krylov.XR
noncomputable section

/-- All three sufficient primitive Radau smallness inequalities hold
on one positive radius uniformly over every stored window length p≤n.
Article: main_krylov, apG:radau-adequate, epsilon_R. -/
theorem radau_uniform_radius (n : ℕ) (mu a b upper sigma : ℝ)
    (ha : 0<a) (hb : 0<b) (hs : 0<sigma) (hm : mu<a) (hu : b<upper) :
    ∃ r : ℝ,0<r ∧ ∀ p : ℕ,p≤n → ∀ epsilon : ℝ,0≤epsilon → epsilon≤r →
      Real.sqrt p*epsilon≤a*sigma^2/2 ∧
      (p+1 : ℕ)*epsilon<(a-mu)*(a*sigma^2/(2*b)) ∧
      (p+1 : ℕ)*epsilon<(upper-b)*(a*sigma^2/(2*b)) := by
  let gamma := a*sigma^2/(2*b)
  let C := min (a*sigma^2/2) (min ((a-mu)*gamma) ((upper-b)*gamma))
  let D := max 1 (max (Real.sqrt n) (n+1 : ℝ))
  have hg : 0<gamma := by dsimp only [gamma];positivity
  have hC : 0<C := by
    dsimp only [C]
    exact lt_min (by positivity)
      (lt_min (mul_pos (sub_pos.mpr hm) hg) (mul_pos (sub_pos.mpr hu) hg))
  have hD : 0<D := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  refine ⟨C/(2*D),by positivity,?_⟩
  intro p hp epsilon he hr
  have hscaled : D*epsilon≤C/2 := by
    have hh := mul_le_mul_of_nonneg_left hr hD.le
    convert hh using 1
    field_simp
  have hsn : Real.sqrt p≤D :=
    (Real.sqrt_le_sqrt (by exact_mod_cast hp)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  have hpn : (p+1 : ℝ)≤D := by
    have hh : (p : ℝ)≤n := by exact_mod_cast hp
    exact (by linarith : (p+1 : ℝ)≤n+1).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hpp : (p+1 : ℕ)*epsilon≤C/2 := by
    have hh := (mul_le_mul_of_nonneg_right hpn he).trans hscaled
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  refine ⟨((mul_le_mul_of_nonneg_right hsn he).trans hscaled).trans
    ((by linarith : C/2≤C).trans (min_le_left _ _)),?_,?_⟩
  · exact hpp.trans_lt ((by linarith : C/2<C).trans_le
      ((min_le_right _ _).trans (min_le_left _ _)))
  · exact hpp.trans_lt ((by linarith : C/2<C).trans_le
      ((min_le_right _ _).trans (min_le_right _ _)))

end
end krylov.XR
