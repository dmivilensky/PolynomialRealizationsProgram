import jacobi.Oscillation.PhaseZeros

/-!
Article: jacobi, Proposition B.1.
The actual restoring solution at angle x/N is rescaled with its literal
first derivative. Every state, measurability and equation field follows
from the original solution. This allows the ordinary phase to be built
for the true finite wave on its Bessel-scaled interval.
Use: instantiates the true scaled finite Jacobi phase for the uniform original-zero estimates.
-/
namespace jacobi.Oscillation.RestoringSolution
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
variable {I : Set ℝ}

/-- The genuine restoring state of the original wave at x/N, with the exact derivative and divided-square potential.
Use: instantiates the true scaled finite Jacobi phase for the uniform original-zero estimates.
Article: jacobi, Proposition B.1.
-/
def rescale (S : RestoringSolution I) (N : ℝ) (hN : 0<N) :
    RestoringSolution ((fun x : ℝ => x/N) ⁻¹' I) where
  value := fun x => S.value (x/N)
  slope := fun x => S.slope (x/N)/N
  potential := fun x => S.potential (x/N)/N^2
  value_measurable := S.value_measurable.comp (by fun_prop)
  slope_measurable := by have h := S.slope_measurable; fun_prop
  potential_measurable := by have h := S.potential_measurable; fun_prop
  potential_continuous := by
    intro x hx
    exact ((S.potential_continuous (x/N) hx).comp (f := fun t : ℝ => t/N) (by fun_prop)).div_const _
  first := by
    intro x hx
    simpa only [Function.comp_def,id_eq,one_div,mul_comm,div_eq_mul_inv,mul_one] using
      (S.first (x/N) hx).comp x ((hasDerivAt_id x).div_const N)
  second := by
    intro x hx
    convert ((S.second (x/N) hx).comp x ((hasDerivAt_id x).div_const N)).div_const N using 1
    · rfl
    · simp only [div_eq_mul_inv,one_mul]
      ring
  nontrivial := by
    intro x hx
    rcases S.nontrivial (x/N) hx with h | h
    · exact Or.inl h
    · exact Or.inr (div_ne_zero h hN.ne')

end
end jacobi.Oscillation.RestoringSolution
