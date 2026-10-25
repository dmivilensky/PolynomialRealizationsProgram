import polyak.FareyPlateau.Ray.SharpCurvature

/-! Equality in the sharp curvature estimate determines the full
finitely supported multiplier, including its two barycentric weights. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels
open scoped BigOperators Classical

theorem SourceCertificate.adjacent_weights {j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (C : SourceCertificate j k b D) (hk : 0<k) (hb : (b*j)%k=1)
    (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k)
    (hsupp : ∀i,C.lag i=n₁ ∨ C.lag i=n₁+k) :
    ∀l : ℤ,LargeCurvature.supportWeight C.lag C.weight l=
      if l=n₁ then 1-t else if l=n₁+k then t else 0 := by
  have hne : n₁≠n₁+k := by omega
  let L := LargeCurvature.supportWeight C.lag C.weight n₁
  let U := LargeCurvature.supportWeight C.lag C.weight (n₁+k)
  have hsum : L+U=1 := by
    rw [←C.admissible.normalization]
    unfold L U LargeCurvature.supportWeight
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hsupp i with hi|hi
    · rw [hi]; simp [hne]
    · rw [hi]; simp [hne.symm]
  have hm : firstMoment C.lag C.weight=(n₁:ℝ)*L+((n₁:ℝ)+k)*U := by
    unfold firstMoment L U LargeCurvature.supportWeight
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hsupp i with hi|hi
    · rw [hi];simp [hne,mul_comm]
    · rw [hi];simp [hne.symm,mul_comm]
  have hclass (i) : C.lag i%k=b%k := by
    rcases hsupp i with hi|hi
    · rw [hi];exact hn₁
    · rw [hi,Int.add_emod_right];exact hn₁
  have hOne : oneClass k b C.lag=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _;exact hclass i
  have hμ : oneMass k b C.lag C.weight=1 := by rw [oneMass,hOne];exact C.admissible.normalization
  have hv : oneMoment k b C.lag C.weight=firstMoment C.lag C.weight := by rw [oneMoment,hOne];rfl
  have hfirst := admissible_moment_balance hb C.admissible
  rw [hμ,hv,hbar,mul_one] at hfirst
  have hmoment : (n₁:ℝ)*L+((n₁:ℝ)+k)*U=(n₁:ℝ)+t*k := by linarith [hm]
  have hU : U=t := by
    have heq : (k:ℝ)*(U-t)=0 := by linear_combination hmoment-(n₁:ℝ)*hsum
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (by exact_mod_cast hk.ne'))
  have hL : L=1-t := by linarith
  intro l
  by_cases hl : l=n₁
  · rw [ite_eq_left hl,hl];exact hL
  by_cases hu : l=n₁+k
  · rw [ite_eq_right hl,ite_eq_left hu,hu];exact hU
  rw [ite_eq_right hl,ite_eq_right hu]
  unfold LargeCurvature.supportWeight
  apply Finset.sum_eq_zero
  intro i _
  have hi : C.lag i≠l := by
    rcases hsupp i with h|h
    · rw [h];exact Ne.symm hl
    · rw [h];exact Ne.symm hu
  simp [hi]

end polyak.FareyPlateau.Ray
