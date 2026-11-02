import jacobi.GelfandLevitan.MidpointProductGrowth
import jacobi.Complex.CirclePolynomial

/-!
Article: jacobi, Proposition C.2.
The actual original separated-product quotient is constant. Its
entire zero-free extension and its polynomial bounds on the genuine
expanding contours have all been established for the original data.
Cauchy estimates, the actual entire Taylor expansion and the fundamental
theorem of algebra give the global factorization. Boundary identification
and the negative-axis comparison still determine its printed scalar.
Use: midpointProductQuotient_constant applies the proved Cauchy circle-growth theorem to the actual expanding energy contours.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The genuine original energy contour radii diverge to infinity.
Use: midpointProductQuotient_constant applies the proved Cauchy circle-growth theorem to the actual expanding energy contours.
Article: jacobi, Proposition C.2.
Proof: the original frequency radius is at least m+1, and squaring a positive divergent radius preserves divergence. -/
theorem contourEnergyRadius_tendsto (a : ℝ) (ha : -1<a) :
    Tendsto (fun m:ℕ => (contourRadius a m)^2) atTop atTop := by
  have hi : Tendsto (fun m:ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto (contourRadius a) atTop atTop :=
    tendsto_atTop_mono (contourRadius_index_le ha) hi
  exact (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp hR

/-- The actual original separated-product quotient is constant on the full complex energy plane.
Use: separatedProduct_factorization is the genuine full characteristic factorization before the subsequent exact boundary and scalar identification.
Article: jacobi, Proposition C.2.
Proof: the genuine quotient is entire and zero-free by the independently proved exhaustive simple zero sets. Its actual contour estimate is polynomial. Cauchy estimates truncate its entire Taylor series to a polynomial; the fundamental theorem of algebra then makes that zero-free polynomial constant. -/
theorem midpointProductQuotient_constant (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointProductQuotient a ha z=
      midpointProductQuotient a ha (jacobi.Jacobi.endpointCorrection a:ℂ) := by
  -- All analytic, multiplicity and circle-growth hypotheses are proved for the unchanged original midpoint functions.
  obtain ⟨C,_,N,hbound⟩ := midpointProductQuotient_circle_bound a ha
  exact jacobi.Complex.circle_power_bound_zero_free_constant
    (fun w => (midpointProductQuotient_analytic a ha w).differentiableAt)
    (midpointProductQuotient_ne_zero a ha) (jacobi.Jacobi.endpointCorrection a:ℂ)
    (contourEnergyRadius_tendsto a ha) C N hbound z

/-- The product of the actual two original separated midpoint characteristics is a fixed nonzero multiple of the exact original Bessel characteristic at every complex energy.
Use: the negative-axis and boundary-class comparison determines the precise printed Neumann/Dirichlet characteristics and their kappa normalization in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: evaluate the genuine entire quotient at the fixed original reference correction. It is nonzero, constant by the proved contour-growth argument, and its independently proved global division identity multiplies back to the unchanged original separated product everywhere. -/
theorem separatedProduct_factorization (a : ℝ) (ha : -1<a) :
    ∃ C:ℂ,C≠0 ∧ ∀ z,separatedCharacteristic a ha 0 z*separatedCharacteristic a ha 1 z=
      C*characteristicSigma a z := by
  refine ⟨midpointProductQuotient a ha (jacobi.Jacobi.endpointCorrection a:ℂ),
    midpointProductQuotient_ne_zero a ha _,fun z => ?_⟩
  have h := midpointProductQuotient_factor a ha z
  rw [midpointProductQuotient_constant] at h
  exact h.symm

end
end jacobi.GelfandLevitan
