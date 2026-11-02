import krylov.Design.SechExtremum
import krylov.Design.EvenIntegerSums
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Article: main_krylov, apC:lem:poisson, an elementary route to elliptic nome identities.
Use: prove the genuine integer-lattice sech convolution from telescoping tanh
increments. All sums are actual convergent sums; no elliptic or theta identity
is assumed. This is the hyperbolic addition formula plus discrete telescoping.
Source: elementary hyperbolic addition and mathlib's unconditional-series rules.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped Topology

/-- The genuine tanh difference equals the product of the two actual secants.
Article: main_krylov, apC:lem:poisson, the hyperbolic convolution calculation. -/
theorem tanh_sub_eq_sech_product (x y : ℝ) :
    tanh x - tanh y = sinh (x - y) * sech x * sech y := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
  unfold jacobi.Young.sech
  field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne']

/-- The actual one-sided tanh lattice increments sum to one.
Article: main_krylov, apC:lem:poisson, the discrete primitive for sech convolution. -/
theorem tanh_nat_lattice_increment {θ : ℝ} (hθ : 0 < θ) :
    HasSum (fun n : ℕ => tanh (((n : ℝ) + 1) * θ) - tanh ((n : ℝ) * θ)) 1 := by
  have hn (n : ℕ) : 0 ≤ tanh (((n : ℝ) + 1) * θ) - tanh ((n : ℝ) * θ) := by
    apply sub_nonneg.mpr
    exact tanh_strictMono.monotone (by nlinarith)
  apply (hasSum_iff_tendsto_nat_of_nonneg hn 1).mpr
  have hN : Tendsto (fun n : ℕ => (n : ℝ) * θ) atTop atTop := by
    simpa only [mul_comm θ] using
      Filter.Tendsto.const_mul_atTop hθ (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := tanh_atTop.comp hN
  convert! ht using 1
  funext N
  have he : (fun n : ℕ => tanh (((n : ℝ) + 1) * θ) - tanh ((n : ℝ) * θ)) =
      (fun n : ℕ => tanh ((n + 1 : ℕ) * θ) - tanh ((n : ℝ) * θ)) := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [he, Finset.sum_range_sub (fun n : ℕ => tanh ((n : ℝ) * θ)) N]
  simp only [Nat.cast_zero, zero_mul, Real.tanh_zero, sub_zero, Function.comp_def]

/-- The actual full integer-lattice tanh increments sum to two.
Article: main_krylov, apC:lem:poisson, the exact whole-line discrete primitive. -/
theorem tanh_integer_lattice_increment {θ : ℝ} (hθ : 0 < θ) :
    HasSum (fun n : ℤ => tanh ((n + 1 : ℤ) * θ) - tanh ((n : ℝ) * θ)) 2 := by
  have hp : HasSum (fun n : ℕ => tanh (((n : ℤ) + 1 : ℤ) * θ) - tanh ((n : ℤ) * θ)) 1 := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using tanh_nat_lattice_increment hθ
  have hn : HasSum (fun n : ℕ =>
      tanh ((-((n : ℤ) + 1) + 1 : ℤ) * θ) - tanh ((-((n : ℤ) + 1) : ℤ) * θ)) 1 := by
    convert! tanh_nat_lattice_increment hθ using 1
    funext n
    simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    rw [show (-((n : ℝ) + 1) + 1) * θ = -((n : ℝ) * θ) by ring,
      neg_mul, Real.tanh_neg, Real.tanh_neg]
    ring
  simpa only [one_add_one_eq_two] using
    (HasSum.of_nat_of_neg_add_one
      (f := fun n : ℤ => tanh ((n + 1 : ℤ) * θ) - tanh ((n : ℝ) * θ)) hp hn)

/-- Any actual integer translate of tanh has the precise total lattice increment 2*k.
Article: main_krylov, apC:lem:poisson, the discrete hyperbolic convolution primitive. -/
theorem tanh_integer_lattice_translate {θ : ℝ} (hθ : 0 < θ) (k : ℤ) :
    HasSum (fun n : ℤ => tanh (((n + k : ℤ) : ℝ) * θ) - tanh ((n : ℝ) * θ)) (2 * (k : ℝ)) := by
  let T : ℤ → ℝ := fun n => tanh ((n : ℝ) * θ)
  have hd : HasSum (fun n : ℤ => T (n + 1) - T n) 2 := tanh_integer_lattice_increment hθ
  change HasSum (fun n : ℤ => T (n + k) - T n) (2 * (k : ℝ))
  have hnat (j : ℕ) : HasSum (fun n : ℤ => T (n + (j : ℤ)) - T n) (2 * (j : ℝ)) := by
    induction j with
    | zero => simp only [add_zero, sub_self, Nat.cast_zero, mul_zero, hasSum_zero]
    | succ j ih =>
      have hh := (Equiv.addRight (j : ℤ)).hasSum_iff.mpr hd
      have hs := ih.add hh
      convert! hs using 1
      · funext n
        simp only [Nat.cast_add, Nat.cast_one, Function.comp_def, Equiv.coe_addRight]
        rw [add_assoc]
        ring
      · push_cast
        ring
  cases k with
  | ofNat j => exact hnat j
  | negSucc j =>
    have hh := (Equiv.addRight (-((j + 1 : ℕ) : ℤ))).hasSum_iff.mpr (hnat (j + 1))
    have hs := hh.neg
    convert! hs using 1
    · funext n
      change T (n + Int.negSucc j) - T n =
        -(T ((n + -((j + 1 : ℕ) : ℤ)) + ((j + 1 : ℕ) : ℤ)) - T (n + -((j + 1 : ℕ) : ℤ)))
      rw [show n + -((j + 1 : ℕ) : ℤ) + ((j + 1 : ℕ) : ℤ) = n by ring]
      rw [show Int.negSucc j = -((j + 1 : ℕ) : ℤ) by rfl]
      ring
    · push_cast
      ring

/-- The exact actual integer-lattice secant correlation at every nonzero integer translate.
Article: main_krylov, apC:lem:poisson, a hyperbolic route to AGM duplication.
Proof: divide the genuine telescoping tanh sum by its nonzero sinh factor. -/
theorem sech_lattice_correlation {θ : ℝ} (hθ : 0 < θ) {k : ℤ} (hk : k ≠ 0) :
    HasSum (fun n : ℤ => sech ((n : ℝ) * θ) * sech (((n + k : ℤ) : ℝ) * θ))
      (2 * (k : ℝ) / sinh ((k : ℝ) * θ)) := by
  have hkθ : (k : ℝ) * θ ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) hθ.ne'
  have hs := (tanh_integer_lattice_translate hθ k).div_const (sinh ((k : ℝ) * θ))
  convert! hs using 1
  funext n
  rw [tanh_sub_eq_sech_product,
    show ((n + k : ℤ) : ℝ) * θ - (n : ℝ) * θ = (k : ℝ) * θ by push_cast; ring]
  field_simp [Real.sinh_ne_zero.mpr hkθ]

end
end krylov.Design
