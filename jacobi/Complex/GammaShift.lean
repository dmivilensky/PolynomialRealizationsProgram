import jacobi.Complex.GammaModulus

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's Gamma recurrence and the reverse triangle inequality.
Use: extends gamma_shift_product to arbitrary real shifts at large complex frequencies, needed after Euler reflection in Delta_tau.
-/
namespace jacobi.Complex
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The finite Gamma recurrence holds whenever its finitely many actual recurrence factors are nonzero.
Use: extends gamma_shift_product to arbitrary real shifts at large complex frequencies, needed after Euler reflection in Delta_tau.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's Gamma recurrence.
Proof: induct on the finite product length and apply Gamma_add_one at the final nonzero factor. -/
theorem gamma_rising_product (w : ℂ) (n : ℕ) (hn : ∀ j<n,w+(j:ℂ)≠0) :
    Gamma (w+(n:ℂ))=Gamma w*∏ j∈Finset.range n,(w+(j:ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,Gamma_add_one _ (hn n (Nat.lt_succ_self n)),
      ih (fun j hj => hn j (hj.trans (Nat.lt_succ_self n))),Finset.prod_range_succ]
    ring

/-- Every factor of a fixed real rising product is between half and twice the frequency outside one fixed disk.
Use: rising_product_bounds controls the finite Gamma factors introduced when shifting the reflected characteristic's arguments to positive real parts.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the norm of the real offset a+j is at most abs(a)+n; both triangle inequalities compare the shifted factor with norm(z). -/
theorem rising_factor_bounds (a : ℝ) (n : ℕ) (z : ℂ)
    (hz : 2*(|a|+(n:ℝ)+1)≤‖z‖) {j : ℕ} (hj : j<n) :
    ‖z‖/2≤‖z+(a:ℂ)+(j:ℂ)‖ ∧ ‖z+(a:ℂ)+(j:ℂ)‖≤2*‖z‖ := by
  -- The threshold is independent of the factor index throughout the original finite product.
  have hjn : (j:ℝ)≤n := by exact_mod_cast hj.le
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hc : ‖(a:ℂ)+(j:ℂ)‖≤|a|+(n:ℝ) := by
    calc
      _ ≤ ‖(a:ℂ)‖+‖(j:ℂ)‖ := norm_add_le _ _
      _ = |a|+(j:ℝ) := by simp [Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by linarith
  have hu := norm_add_le z ((a:ℂ)+(j:ℂ))
  have hl : ‖z‖≤‖z+((a:ℂ)+(j:ℂ))‖+‖(a:ℂ)+(j:ℂ)‖ := by
    simpa using norm_sub_le (z+((a:ℂ)+(j:ℂ))) ((a:ℂ)+(j:ℂ))
  rw [← add_assoc] at hu hl
  constructor <;> linarith [norm_nonneg z,abs_nonneg a]

/-- The full finite rising product has matching frequency-power bounds outside one fixed disk.
Use: gamma_tail_power_bounds cancels the numerator and denominator finite shifts while retaining the sharp Gamma quotient power law.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: multiply the genuine factor bounds over the finite index range; all lower bounds are nonnegative. -/
theorem rising_product_bounds (a : ℝ) (n : ℕ) (z : ℂ)
    (hz : 2*(|a|+(n:ℝ)+1)≤‖z‖) :
    (‖z‖/2)^n≤‖∏ j∈Finset.range n,(z+(a:ℂ)+(j:ℂ))‖ ∧
      ‖∏ j∈Finset.range n,(z+(a:ℂ)+(j:ℂ))‖≤(2*‖z‖)^n := by
  rw [norm_prod]
  constructor
  · simpa only [Finset.prod_const,Finset.card_range] using Finset.prod_le_prod₀ (s := Finset.range n)
      (f := fun _ : ℕ => ‖z‖/2) (g := fun j : ℕ => ‖z+(a:ℂ)+(j:ℂ)‖)
      (fun _ _ => by positivity) (fun j hj => (rising_factor_bounds a n z hz (Finset.mem_range.mp hj)).1)
  · simpa only [Finset.prod_const,Finset.card_range] using Finset.prod_le_prod₀ (s := Finset.range n)
      (f := fun j : ℕ => ‖z+(a:ℂ)+(j:ℂ)‖) (g := fun _ : ℕ => 2*‖z‖)
      (fun _ _ => norm_nonneg _) (fun j hj => (rising_factor_bounds a n z hz (Finset.mem_range.mp hj)).2)

/-- Two positive finite-shift product norms have a uniformly bounded ratio when each has the same frequency-power bounds.
Use: gamma_tail_power_bounds cancels the finite Gamma shifts with constants independent of the original complex frequency.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: divide the upper product bound by the lower one and conversely; the frequency powers cancel to 4^n and (1/4)^n. -/
theorem shift_ratio_bounds {r x y : ℝ} (hr : 0<r) (hx : 0<x) (hy : 0<y) (n : ℕ)
    (hxl : (r/2)^n≤x) (hxu : x≤(2*r)^n)
    (hyl : (r/2)^n≤y) (hyu : y≤(2*r)^n) :
    (1/4:ℝ)^n≤y/x ∧ y/x≤(4:ℝ)^n := by
  -- Positivity is retained before dividing either finite product estimate.
  have hlow : 0<(r/2)^n := by positivity
  have hl := div_le_div₀ hy.le hyl hx hxu
  have hu := div_le_div₀ (by positivity : 0≤(2*r)^n) hyu hlow hxl
  have hel : (r/2)^n/(2*r)^n=(1/4:ℝ)^n := by rw [← div_pow]; congr 1; field_simp [hr.ne']; norm_num
  have heu : (2*r)^n/(r/2)^n=(4:ℝ)^n := by rw [← div_pow]; congr 1; field_simp [hr.ne']; norm_num
  exact ⟨hel ▸ hl,heu ▸ hu⟩

end
end jacobi.Complex
