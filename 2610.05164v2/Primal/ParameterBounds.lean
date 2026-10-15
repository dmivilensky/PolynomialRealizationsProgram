import «2610.05164v2».Primal.Family
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.Normed.Group.Constructions

/-!
Article: 2610.05164v2, Theorem 5.2.
Chebyshev unit-interval bounds and the six-direction profile perturbation estimate.
Use: `«2610.05164v2».Primal.profile_difference_bound` feeds
`«2610.05164v2».Primal.family_energy_ceiling` (family energy ceiling).
Source: mathlib, Polynomial.Chebyshev.abs_eval_T_real_le_one — Chebyshev bound on [-1,1].
-/
namespace «2610.05164v2».Primal
noncomputable section
open Polynomial Set
set_option autoImplicit false

/--
The stated quantitative bound `|(chebyshevDirection j).eval t|≤1`.

Use: `«2610.05164v2».Primal.profile_difference_bound` uses this bound to establish the stated
quantitative bound `|profile c directions a t-profile c directions b t|≤6*ρ`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.profile_difference_bound`.

Source: mathlib, Polynomial.Chebyshev.abs_eval_T_real_le_one — Chebyshev bound on [-1,1].

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem chebyshev_bound (j : Nat) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |(chebyshevDirection j).eval t|≤1 := by
  simpa [chebyshevDirection] using
    Polynomial.Chebyshev.abs_eval_T_real_le_one (j:ℤ) (x := 2*t-1)
      (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)

/--
The stated quantitative bound `|profile c directions a t-profile c directions b t|≤6*ρ`.

Use: `«2610.05164v2».Primal.family_energy_ceiling` uses this bound to establish the stated
quantitative bound `(∫ x,(familySpeed c directions a).density κ x^(3/2:ℝ))≤ exp (6*ρ)*(∫
x,(familySpeed c directions 0).density κ x^(3/2:ℝ))`.

Article: 2610.05164v2, Theorem 5.2.

Source: mathlib, Polynomial.Chebyshev.abs_eval_T_real_le_one — Chebyshev bound on [-1,1].

Proof: Use the identities/estimates `«2610.05164v2».Primal.chebyshev_bound` with the arguments
shown in the proof.
-/
theorem profile_difference_bound (c : Fin 17 → ℝ) (directions : Fin 6 → Nat)
    {a b : Fin 6 → ℝ} {ρ t : ℝ} (hab : ‖a-b‖≤ρ) (ht : t∈Icc (0:ℝ) 1) :
    |profile c directions a t-profile c directions b t|≤6*ρ := by
  -- Use the identities/estimates `«2610.05164v2».Primal.chebyshev_bound` with the arguments
  -- shown in the proof.
  have he : profile c directions a t-profile c directions b t=
      ∑ i : Fin 6,(a i-b i)*(chebyshevDirection (directions i)).eval t := by
    simp only [profile,familyPolynomial,eval_add,eval_finsetSum,eval_mul,eval_C]
    simp_rw [sub_mul,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    |∑ i : Fin 6,(a i-b i)*(chebyshevDirection (directions i)).eval t|≤
        ∑ i : Fin 6,|(a i-b i)*(chebyshevDirection (directions i)).eval t| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ _i : Fin 6,ρ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have ha : |a i-b i|≤ρ := by
        simpa only [Real.norm_eq_abs,Pi.sub_apply] using (norm_le_pi_norm (a-b) i).trans hab
      exact (mul_le_mul_of_nonneg_left (chebyshev_bound _ ht) (abs_nonneg _)).trans
        (by simpa using ha)
    _=6*ρ := by simp

end
end «2610.05164v2».Primal
