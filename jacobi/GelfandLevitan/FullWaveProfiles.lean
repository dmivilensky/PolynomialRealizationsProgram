import jacobi.GelfandLevitan.FullWaveMaps
import jacobi.GelfandLevitan.ProfileBounds

/-!
Article: jacobi, Theorem 2.1.
The actual continuous full target waves have exactly the original
profile squares and one common uniform bound. These are the pointwise
estimates that make the genuine Green kernel series converge uniformly
on the entire closed physical square, including the midpoint lines.
Use: targetGreen_diagonal and targetGreenKernelTerm_norm_bound identify the genuine Green diagonal and prove the original full-square uniform convergence.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The pointwise square of every actual continuous full target wave is exactly the original reflected spectral profile.
Use: targetGreen_diagonal and targetGreenKernelTerm_norm_bound identify the genuine Green diagonal and prove the original full-square uniform convergence.
Article: jacobi, Theorem 2.1.
Proof: on the physical left half, folding is the original coordinate and the squared genuine normalization is rho_k/N_k. On the right half, folding is its actual reflection and the original reflection sign has square one. Both cases include the unchanged midpoint value. -/
theorem fullWaveMap_sq (a : ℝ) (ha : -1<a) (n : ℕ) (t : Interval) :
    (fullWaveMap a ha n t)^2=spectralProfile a ha n t := by
  -- Pointwise equality at the midpoint is meaningful because the actual continuous Dirichlet gluing was proved before this normalization calculation.
  have hsign : ((-1:ℝ)^n)^2=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  by_cases hp : (t:ℝ)≤1/2
  · have hfold : physicalFold t=halfClamp t := by
      apply Subtype.ext
      change min (t:ℝ) (1-(t:ℝ))=min (t:ℝ) (1/2)
      rw [min_eq_left (by linarith),min_eq_left hp]
    change (targetWaveScale a ha n*(if (t:ℝ)≤1/2 then _ else _))^2=
      (normingRatio a ha n/norming a n)*
        (realTransformedSolution a ha (jacobi.Bessel.sigma a ha n) (physicalFold t))^2
    rw [ite_eq_left hp,mul_pow,targetWaveScale_sq,hfold]
    rfl
  · have hfold : physicalFold t=halfClamp (physicalReflection t) := by
      apply Subtype.ext
      change min (t:ℝ) (1-(t:ℝ))=min (1-(t:ℝ)) (1/2)
      rw [min_eq_right (by linarith [lt_of_not_ge hp]),min_eq_left (by linarith [lt_of_not_ge hp])]
    change (targetWaveScale a ha n*(if (t:ℝ)≤1/2 then _ else _))^2=
      (normingRatio a ha n/norming a n)*
        (realTransformedSolution a ha (jacobi.Bessel.sigma a ha n) (physicalFold t))^2
    rw [ite_eq_right hp,mul_pow,mul_pow,hsign,one_mul,targetWaveScale_sq,hfold]
    rfl

/-- One genuine positive constant uniformly bounds every actual full continuous target wave in the original spatial supremum norm.
Use: the actual inverse-sigma series dominates all continuous Green kernel terms on the entire original physical square.
Article: jacobi, Theorem 2.1.
Proof: the original profiles have a proved all-index positive uniform bound D. Since each actual wave square is that same profile, its norm is bounded by sqrt(D). -/
theorem fullWaveMap_uniform_bound (a : ℝ) (ha : -1<a) :
    ∃ D:ℝ,0<D ∧ ∀ n:ℕ,‖fullWaveMap a ha n‖≤D := by
  -- The finite original spectral prefix was already absorbed analytically in the actual profile bound, so no numerical exception remains here.
  obtain ⟨D,hD,hbound⟩ := spectralProfile_uniform_bound a ha
  refine ⟨Real.sqrt D,Real.sqrt_pos.mpr hD,fun n => ?_⟩
  apply ((fullWaveMap a ha n).norm_le (Real.sqrt_nonneg D)).mpr
  intro t
  have hs : (fullWaveMap a ha n t)^2≤D := by
    rw [fullWaveMap_sq]
    exact (le_abs_self _).trans (((spectralProfile a ha n).norm_coe_le_norm t).trans (hbound n))
  rw [Real.norm_eq_abs]
  nlinarith [Real.sq_sqrt hD.le,Real.sqrt_nonneg D,sq_abs (fullWaveMap a ha n t),abs_nonneg (fullWaveMap a ha n t)]

end
end jacobi.GelfandLevitan
