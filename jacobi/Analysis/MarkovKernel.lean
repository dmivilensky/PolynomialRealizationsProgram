import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
Article: jacobi, Proposition 2.2.
A continuous symmetric kernel with nonzero diagonal and transitive
nonvanishing has no zero entry on a connected domain. For an ordered
Markov kernel, transitivity follows directly from its exact three-point identity.
Use: Trichotomy.GreenPositivity applies both statements to the actual
continuum kernel inherited from finite Jacobi inverses.
Source: the clopen-class argument for continuous Markov kernels, proved here.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter
open scoped Topology

/-- On a linearly ordered domain, a symmetric kernel with nonzero diagonal and the ordered Markov identity has transitive nonvanishing.
Use: the actual target Green kernel supplies a continuous nonvanishing equivalence relation on the connected physical interval.
Article: jacobi, Proposition 2.2.
Proof: order the two outer points. The middle point lies before, inside or after their interval. In each case the exact Markov identity puts a nonzero diagonal times a known nonzero entry on one side, forcing the required outer entry to be nonzero. -/
theorem markov_nonzero_transitive {X:Type*} [LinearOrder X] {G:X→X→ℝ}
    (hsym:∀ x y,G x y=G y x) (hd:∀ x,G x x≠0)
    (hm:∀ x y z,x≤y → y≤z → G x z*G y y=G x y*G y z)
    (x y z:X) (hxy:G x y≠0) (hyz:G y z≠0) : G x z≠0 := by
  -- Only the exact three-point identity and a nonzero genuine diagonal are used.
  have ho (x y z:X) (hxz:x≤z) (hxy:G x y≠0) (hyz:G y z≠0) : G x z≠0 := by
    rcases le_total y x with hyx | hxy'
    · have he := hm y x z hyx hxz
      intro hz
      rw [hz,mul_zero] at he
      exact mul_ne_zero hyz (hd x) he
    · rcases le_total y z with hyz' | hzy
      · have he := hm x y z hxy' hyz'
        intro hz
        rw [hz,zero_mul] at he
        exact mul_ne_zero hxy hyz he.symm
      · have he := hm x z y hxz hzy
        intro hz
        rw [hz,zero_mul] at he
        exact mul_ne_zero hxy (hd z) he
  rcases le_total x z with hxz | hzx
  · exact ho x y z hxz hxy hyz
  · rw [hsym x z]
    apply ho z y x hzx
    · simpa only [hsym z y] using hyz
    · simpa only [hsym y x] using hxy

/-- Every entry of a connected continuous symmetric kernel with nonzero diagonal and transitive nonvanishing is nonzero.
Use: strict positivity of the actual canonical Green kernel follows from its nonnegativity, with no unproved differential-kernel premise.
Article: jacobi, Proposition 2.2.
Proof: a fixed row's nonzero set is open by continuity. Near a zero entry, the diagonal gives a nonzero neighboring row; transitivity excludes nonzero fixed-row entries nearby, so the complement is open as well. Connectedness and the nonzero diagonal make this clopen class the full domain. -/
theorem continuous_kernel_nonzero {X:Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {G:X→X→ℝ} (hc:Continuous (fun p:X × X => G p.1 p.2))
    (hsym:∀ x y,G x y=G y x) (hd:∀ x,G x x≠0)
    (htrans:∀ x y z,G x y≠0 → G y z≠0 → G x z≠0) (x y:X) : G x y≠0 := by
  -- The complement is open by the actual local nonzero diagonal, so connectedness propagates the same row globally.
  let S : Set X := {z | G x z≠0}
  have hrow (u:X) : Continuous (G u) := hc.comp (continuous_const.prodMk continuous_id)
  have hS : IsOpen S := isOpen_ne.preimage (hrow x)
  have hC : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have he : ∀ᶠ w in 𝓝 z,G z w≠0 := (isOpen_ne.preimage (hrow z)).mem_nhds (hd z)
    apply Filter.mem_of_superset he
    intro w hzw
    change ¬G x w≠0
    intro hxw
    exact hz (htrans x w z hxw (by rwa [hsym w z]))
  have hAll : S=univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hC,hS⟩).eq_univ ⟨x,hd x⟩
  have : y∈S := by rw [hAll]; trivial
  exact this

end
end jacobi.Analysis
