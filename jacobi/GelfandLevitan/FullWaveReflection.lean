import jacobi.GelfandLevitan.FullWaveMaps

/-!
Article: jacobi, Theorem 2.1.
The genuine continuous full waves restrict to the normalized original
half solutions and have the exact signed physical reflection, including
the midpoint. These identities connect the finite eigenvector parity
with the same continuous representatives of the actual full operator.
Use: the uniform finite half-chain eigenvector limit is compared with the same continuous full wave appearing in Theorem 2.1.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference

/-- The genuine full continuous wave restricts to its original normalized
half solution, including both endpoints of the physical half interval.
Use: the uniform finite half-chain eigenvector limit is compared with
the same continuous full wave appearing in Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: the original reflection definition chooses its left branch and
the original half clamp fixes that actual coordinate. -/
theorem fullWaveMap_half (a:ℝ) (ha:-1<a) (k:ℕ) (t:Interval) (ht:(t:ℝ)≤1/2) :
    fullWaveMap a ha k t=targetWaveScale a ha k*
      realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) ⟨t.val,⟨t.property.1,ht⟩⟩ := by
  have hc : halfClamp t=(⟨t.val,⟨t.property.1,ht⟩⟩:HalfInterval) :=
    Subtype.ext (min_eq_left ht)
  change targetWaveScale a ha k*(if (t:ℝ)≤1/2 then
    (transformedSolution a ha (halfClamp t) (jacobi.Bessel.sigma a ha k:ℂ)).re else _)=_
  rw [ite_eq_left ht,hc]
  rfl

/-- The genuine continuous full eigenfunctions have the same signed
reflection as the original finite persymmetric eigenvectors.
Use: uniform eigenvector approximation extends to the full physical
chain; the one-cell discrepancy of finite reversal then vanishes by
continuity of this same actual full wave.
Article: jacobi, Theorem 2.1.
Proof: away from the midpoint reflection exchanges the two original
branches, and its square is the identity. At the midpoint the already
proved Dirichlet/even compatibility gives exactly the same signed value. -/
theorem fullWaveMap_reflection (a:ℝ) (ha:-1<a) (k:ℕ) (t:Interval) :
    fullWaveMap a ha k (physicalReflection t)=(-1:ℝ)^k*fullWaveMap a ha k t := by
  -- The midpoint compatibility is essential for the true odd eigenfunctions.
  have hrr : physicalReflection (physicalReflection t)=t := Subtype.ext (by
    change 1-(1-(t:ℝ))=(t:ℝ); ring)
  have hs : (-1:ℝ)^k*((-1:ℝ)^k)=1 := by rw [← pow_two,← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  by_cases he:(t:ℝ)=1/2
  · have hr : physicalReflection t=t := Subtype.ext (by change 1-(t:ℝ)=(t:ℝ); linarith)
    have hc : (⟨t.val,⟨t.property.1,he.le⟩⟩:HalfInterval)=halfMidpoint := Subtype.ext he
    rw [hr,fullWaveMap_half a ha k t he.le]
    change targetWaveScale a ha k*(transformedSolution a ha _ _).re=
      (-1:ℝ)^k*(targetWaveScale a ha k*(transformedSolution a ha _ _).re)
    rw [hc]
    have hp := transformed_midpoint_value_parity a ha k
    nlinarith [congrArg (fun x:ℝ => targetWaveScale a ha k*x) hp]
  · by_cases ht:(t:ℝ)≤1/2
    · have hr : ¬(physicalReflection t:ℝ)≤1/2 := by
        change ¬1-(t:ℝ)≤1/2
        have hlt := lt_of_le_of_ne ht he
        linarith
      change targetWaveScale a ha k*(if (physicalReflection t:ℝ)≤1/2 then _ else _)=
        (-1:ℝ)^k*(targetWaveScale a ha k*(if (t:ℝ)≤1/2 then _ else _))
      rw [ite_eq_right hr,ite_eq_left ht,hrr]
      ring
    · have hr : (physicalReflection t:ℝ)≤1/2 := by
        change 1-(t:ℝ)≤1/2
        linarith [lt_of_not_ge ht]
      change targetWaveScale a ha k*(if (physicalReflection t:ℝ)≤1/2 then _ else _)=
        (-1:ℝ)^k*(targetWaveScale a ha k*(if (t:ℝ)≤1/2 then _ else _))
      rw [ite_eq_left hr,ite_eq_right ht]
      nlinarith [congrArg (fun x:ℝ => x*(targetWaveScale a ha k*
        transformedRealWave a ha (jacobi.Bessel.sigma a ha k) (physicalReflection t))) hs]

end
end jacobi.GelfandLevitan
