import polyak.FareyPlateau.Symbols.PhaseFloor
import Mathlib.RingTheory.PrincipalIdealDomain

/-! The integer Bezout input used for denominator positivity follows
from the literal gcd-one support condition in Definition admissible. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem supportBezout_of_gcd (n : I→ℤ) (w : I→ℝ)
    (hg : (Finset.univ.filter (fun i=>w i≠0)).gcd n=1) : SupportBezout n w := by
  classical
  let N := Finset.univ.filter (fun i=>w i≠0)
  obtain ⟨z,hz⟩ := Finset.gcd_eq_sum_mul N n
  let z' := fun i=>if i∈N then z i else 0
  refine ⟨z',?_,?_⟩
  · intro i hi
    simp [z',N,hi]
  · have hsum : (∑i,z' i*n i)=∑i∈N,n i*z i := by
      rw [←Finset.sum_subset (Finset.subset_univ N) (f:=fun i=>z' i*n i)]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [z',hi,mul_comm]
      · intro i _ hi
        simp [z',hi]
    rw [hsum,←hz]
    exact hg

theorem supportGcd_of_bezout (n : I→ℤ) (w : I→ℝ) (hb : SupportBezout n w) :
    (Finset.univ.filter (fun i=>w i≠0)).gcd n=1 := by
  classical
  rcases hb with ⟨z,hz,hsum⟩
  let N := Finset.univ.filter (fun i=>w i≠0)
  have hd : N.gcd n∣(1:ℤ) := by
    rw [←hsum]
    apply Finset.dvd_sum
    intro i _
    by_cases hi : i∈N
    · exact dvd_mul_of_dvd_right (Finset.gcd_dvd hi) _
    · have hwi : w i=0 := by simpa [N] using hi
      rw [hz i hwi,zero_mul]
      exact dvd_zero _
  have hunit := isUnit_iff_dvd_one.mpr hd
  have hnormalized : normalize (N.gcd n)=N.gcd n := Finset.normalize_gcd
  exact hnormalized.symm.trans (normalize_eq_one.mpr hunit)

end polyak.FareyPlateau.Symbols
