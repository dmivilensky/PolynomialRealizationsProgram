import jacobi.Bessel.McMahonTail

/-!
Article: jacobi, Theorem 2.1.
Elementary scalar estimates replace the reciprocal of an actual zero by
its explicit leading phase and absorb a finite initial segment. They
are applied only after the original Bessel cubic tail has been proved.
Use: turns the actual large-zero McMahon remainder into the article's bound for every original positive index.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine eventual inverse-power estimate extends uniformly across its finite initial segment.
Use: turns the actual large-zero McMahon remainder into the article's bound for every original positive index.
Article: jacobi, Proposition B.1.
Proof: sum the finitely many scaled absolute errors and enlarge the tail
constant. Each initial error is bounded by its own nonnegative sum term. -/
theorem inversePower_bound_all {f : ℕ → ℝ} {C : ℝ} (p : ℕ)
    (he : ∀ᶠ k : ℕ in atTop,|f k|≤C/(k+1:ℝ)^p) :
    ∃ D : ℝ,0<D ∧ ∀ k,|f k|≤D/(k+1:ℝ)^p := by
  -- The finite initial errors are the actual errors of the same function, so this extension imposes no separate numerical certificate.
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  let S := ∑ i∈Finset.range K,|f i| *(i+1:ℝ)^p
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨S+|C|+1,by positivity,?_⟩
  intro k
  have hp : 0<(k+1:ℝ)^p := by positivity
  by_cases hk : K≤k
  · exact (hK k hk).trans (div_le_div_of_nonneg_right (by linarith [le_abs_self C]) hp.le)
  · have hsingle : |f k| *(k+1:ℝ)^p≤S :=
      Finset.single_le_sum (s := Finset.range K) (f := fun i : ℕ => |f i| * (i+1:ℝ)^p)
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
    exact (le_div_iff₀ hp).mpr (hsingle.trans (by linarith [abs_nonneg C]))

/-- Replacing an actual reciprocal zero by a linearly comparable phase preserves a cubic error, with explicit constants.
Use: converts the genuine Bessel phase-invariant estimate into precisely the printed McMahon correction c/(2*varpi).
Article: jacobi, Theorem 2.1.
Proof: the replacement error is c*(v-x)/(2*x*v). Bound its numerator by
the proved inverse-linear error and both positive denominators by their
common linear lower bound; the original cubic error is bounded likewise. -/
theorem reciprocal_correction_bound {x v t d A B c : ℝ} (ht : 0<t) (hd : 0<d)
    (hA : 0≤A) (hB : 0≤B) (hx : d*t≤x) (hv : d*t≤v)
    (hfirst : |x-v|≤A/t) (hcubic : |x-v-c/(2*x)|≤B/x^3) :
    |x-v-c/(2*v)|≤(B/d^3+|c| *A/(2*d^2))/t^3 := by
  -- Only positive scalar denominator estimates are used; the Bessel application supplies every original-function bound.
  have hxp : 0<x := (mul_pos hd ht).trans_le hx
  have hvp : 0<v := (mul_pos hd ht).trans_le hv
  have hprod : (d*t)^2≤x*v := by
    calc
      _ = (d*t)*(d*t) := pow_two _
      _ ≤ x*v := mul_le_mul hx hv (mul_pos hd ht).le hxp.le
  have hid : x-v-c/(2*v)=(x-v-c/(2*x))+(c/2)*((v-x)/(x*v)) := by
    field_simp [hxp.ne',hvp.ne']
    ring
  have hrec : |(v-x)/(x*v)|≤(A/t)/(d*t)^2 := by
    rw [abs_div,abs_sub_comm,abs_of_pos (mul_pos hxp hvp)]
    exact (div_le_div_of_nonneg_right hfirst (mul_pos hxp hvp).le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hprod)
  rw [hid]
  calc
    _ ≤ |x-v-c/(2*x)|+|(c/2)*((v-x)/(x*v))| := abs_add_le _ _
    _ ≤ B/x^3+(|c|/2)*((A/t)/(d*t)^2) := by
      rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add hcubic (mul_le_mul_of_nonneg_left hrec (by positivity))
    _ ≤ B/(d*t)^3+(|c|/2)*((A/t)/(d*t)^2) := by
      apply add_le_add_left
      exact div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_left₀ (by positivity) hx 3)
    _ = _ := by field_simp [hd.ne',ht.ne']

end
end jacobi.Bessel
