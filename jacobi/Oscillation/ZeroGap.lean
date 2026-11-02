import jacobi.Oscillation.Restoring
import jacobi.Bessel.SturmZeros

/-!
Article: jacobi, Proposition B.1.
A true classical restoring solution with coefficient below D^2 cannot
have consecutive zeros separated by at most pi/D. This is proved by
ordinary Sturm comparison with the literal sine wave based at its left
zero. No sign orientation or phase bound is assumed.
Source: the classical Sturm separation/comparison argument.
Use: proves all original Jacobi angular gaps, including the middle gap, from the true endpoint distance estimates.
-/
namespace jacobi.Oscillation.RestoringSolution
noncomputable section
open Real Set jacobi.Bessel
set_option backward.isDefEq.respectTransparency false
variable {I : Set ℝ}

/-- A genuine consecutive-zero interval has length greater than pi/D when its actual restoring coefficient is strictly below D^2.
Use: proves all original Jacobi angular gaps, including the middle gap, from the true endpoint distance estimates.
Article: jacobi, Proposition B.1.
Proof: if the interval were at most pi/D long, the literal sine
sin(D*(x-a)) would be strictly positive throughout its interior.
Genuine Sturm comparison requires an actual comparator zero there,
contradicting that elementary sine sign. -/
theorem zero_gap (S : RestoringSolution I) {a b D : ℝ} (hD : 0<D) (hab : a<b)
    (hI : Icc a b⊆I) (hza : S.value a=0) (hzb : S.value b=0)
    (hno : ∀ x∈Ioo a b,S.value x≠0)
    (hq : ∀ x∈Ioo a b,S.potential x<D^2) : Real.pi<D*(b-a) := by
  -- The comparator is an actual elementary solution; its positive interior sign is derived directly from its argument interval.
  let g := fun x : ℝ => sin (D*(x-a))
  let g' := fun x : ℝ => D*cos (D*(x-a))
  let g'' := fun x : ℝ => -D^2*sin (D*(x-a))
  have hg : ∀ x,HasDerivAt g (g' x) x := by
    intro x
    convert (((hasDerivAt_id x).sub_const a).const_mul D).sin using 1
    · rfl
    · dsimp [g']
      ring
  have hg' : ∀ x,HasDerivAt g' (g'' x) x := by
    intro x
    convert ((((hasDerivAt_id x).sub_const a).const_mul D).cos).const_mul D using 1
    · rfl
    · dsimp [g'']
      ring
  obtain ⟨x,hx,hzx⟩ := sturm_zero_between hab
    (fun t ht => S.first t (hI ht)) (fun t ht => S.second t (hI ht))
    (fun t _ => hg t) (fun t _ => hg' t)
    (fun t _ => by ring) (fun t _ => by dsimp [g,g'']; ring)
    hq hza hzb hno
  by_contra hn
  have ht0 : 0<D*(x-a) := mul_pos hD (sub_pos.mpr hx.1)
  have ht1 : D*(x-a)<Real.pi := by
    have hxt := mul_lt_mul_of_pos_left (sub_lt_sub_right hx.2 a) hD
    exact hxt.trans_le (not_lt.mp hn)
  exact (Real.sin_pos_of_pos_of_lt_pi ht0 ht1).ne' hzx

end
end jacobi.Oscillation.RestoringSolution
