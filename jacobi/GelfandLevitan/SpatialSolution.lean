import jacobi.GelfandLevitan.TransformedBounds
import jacobi.Reference.CoefficientInput

/-!
Article: jacobi, Theorem 2.1.
The original inverse rows are continuous in L2. The same coefficient
integral is continuous in its actual L2 input, so the constructed u
is continuous in the physical variable, including its zero endpoint.
The proved reference spectral decay and common inverse-row bound also
give the actual uniform inverse-index decay used in the profile series.
Use: each original spectral profile is a true continuous function, and finite spectral prefixes have genuine compact bounds in the uniform convergence proof.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual transformed solution is continuous on the entire closed physical half interval at every complex energy.
Use: each original spectral profile is a true continuous function, and finite spectral prefixes have genuine compact bounds in the uniform convergence proof.
Article: jacobi, Theorem 2.1.
Proof: the reference function-space solution is continuous in its
physical coordinate. The actual inverse row is continuous in L2, and
the proved bounded input-linear coefficient functional is continuous
on exactly that original space. Their source sum is the actual u. -/
theorem transformedSolution_continuous (a : ℝ) (ha : -1<a) (z : ℂ) :
    Continuous (fun t:HalfInterval => transformedSolution a ha t z) := by
  -- Point evaluation is used continuously on this fixed actual spatial function; no false operator-norm continuity of varying evaluation functionals is needed.
  have he : (fun t:HalfInterval => halfSolution a ha z (halfInclusion t))=
      (fun t:HalfInterval => solution a z (t:ℝ)) := by
    funext t
    rw [halfSolution_apply]
    exact congrArg (solution a z) (min_eq_left t.property.2)
  have hf : Continuous (fun t:HalfInterval => solution a z (t:ℝ)) := by
    rw [← he]
    exact (halfSolution a ha z).continuous.comp halfInclusion.continuous
  have hv : Continuous (fun t:HalfInterval => (solutionRow a ha t:Space)) :=
    halfSubspace.subtypeL.continuous.comp (solutionRow_continuous a ha)
  have hc : Continuous (fun t:HalfInterval =>
      coefficientFunctional (solutionRow a ha t:Space) (halfSolution a ha z)) :=
    (coefficientInput (halfSolution a ha z)).continuous.comp hv
  have hu : (fun t:HalfInterval => transformedSolution a ha t z)=
      (fun t:HalfInterval => solution a z (t:ℝ)+
        coefficientFunctional (solutionRow a ha t:Space) (halfSolution a ha z)) :=
    funext (fun t => transformedSolution_reference_form a ha t z)
  rw [hu]
  exact hf.add hc

/-- The actual transformed source solution vanishes at the original singular left endpoint for every complex energy.
Use: fixes zero endpoint values of the original spectral profiles and the reflected persymmetric profile.
Article: jacobi, Theorem 2.1.
Proof: the true inverse row is zero at the original endpoint. Its
actual input-linear integral functional therefore vanishes. The
original reference value is zero by its positive sine-power prefactor. -/
theorem transformedSolution_zero (a : ℝ) (ha : -1<a) (z : ℂ) :
    transformedSolution a ha halfZero z=0 := by
  rw [transformedSolution_reference_form,solutionRow_zero]
  have hi : coefficientFunctional (0:Space) (halfSolution a ha z)=0 :=
    (coefficientInput (halfSolution a ha z)).map_zero
  change solution a z 0+coefficientFunctional (0:Space) (halfSolution a ha z)=0
  rw [hi]
  change wave a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) 0+0=0
  rw [wave,(weight_properties ha).2.1,Complex.ofReal_zero,zero_mul,add_zero]

/-- The actual transformed solutions at the original Bessel energies have uniform inverse-index decay over the entire physical half interval.
Use: cancels the true reference norming power in the original spectral profiles and gives their uniform boundedness before summing Lambda_k*Phi_k.
Article: jacobi, Theorem 2.1.
Proof: the actual reference solutions have the proved original uniform
spectral decay. Apply the genuine GL prefix norm estimate with that
same scale and use the common true inverse-row bound. The original
real-energy reality identity equates the real source bound with its
actual complex norm. -/
theorem transformedSolution_spectral_bound (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ k:ℕ in atTop,∀ t:HalfInterval,
      ‖transformedSolution a ha t (jacobi.Bessel.sigma a ha k:ℂ)‖≤C*(k+1:ℝ)^(-gamma a) := by
  -- Every actual small spectral prefix remains finite and continuous; this uniform tail bound supplies the exact original decay scale.
  obtain ⟨A,_,hA,_,hRef⟩ := spectral_solution_bounds ha
  obtain ⟨B,hB,hRows⟩ := solutionRow_bounded a ha
  refine ⟨A*(1+B),by positivity,?_⟩
  filter_upwards [hRef] with k hk t
  have hp : 0≤(k+1:ℝ)^(-gamma a) := Real.rpow_nonneg (by positivity) _
  have hf (r : ℝ) (hr : r∈Icc (0:ℝ) (t:ℝ)) :
      ‖solution a (jacobi.Bessel.sigma a ha k:ℂ) r‖≤A*(k+1:ℝ)^(-gamma a) := by
    rw [← realSolution_cast,Complex.norm_real,Real.norm_eq_abs]
    exact (hk r ⟨hr.1,hr.2.trans t.property.2⟩).1
  calc
    _ ≤ (A*(k+1:ℝ)^(-gamma a))*(1+‖solutionRow a ha t‖) :=
      transformedSolution_norm_le a ha t _ (mul_nonneg hA.le hp) hf
    _ ≤ (A*(k+1:ℝ)^(-gamma a))*(1+B) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (hRows t)) (mul_nonneg hA.le hp)
    _ = _ := by ring

end
end jacobi.GelfandLevitan
