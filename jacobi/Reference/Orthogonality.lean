import jacobi.Reference.Coordinate
import jacobi.Reference.NormRecurrence

/-!
Article: jacobi, Lemma C.1.
Every original reference product has a genuine convergent integral.
The exact original cosine substitution transports it to the already
proved literal Jacobi weighted product, including singular endpoint
weights. Orthogonality and positive reference norming constants follow.
Use: the orthogonality, norming constants and spectral basis are based on convergent integrals.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Every actual reference inner product has a genuinely convergent original integral.
Use: the orthogonality, norming constants and spectral basis are based on convergent integrals.
Article: jacobi, Lemma C.1.
Proof: both original reference eigenfunctions are continuous on the closed physical interval. -/
theorem eigenfunction_product_integrable {a : ℝ} (ha : -1<a) (i j : ℕ) :
    IntervalIntegrable (fun t => eigenfunction a i t*eigenfunction a j t) volume 0 1 :=
  (((eigenfunction_properties ha i).1).mul (eigenfunction_properties ha j).1).intervalIntegrable _ _

/-- The exact original reference inner product equals the literal weighted Jacobi inner product divided by its true coordinate scale.
Use: transports all genuine Jacobi orthogonality and norm evaluation results to the source reference eigenfunctions.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: apply the genuine monotone cosine substitution to the actual
weighted polynomial product. On the physical interior its exact Jacobian
identity is the proved positive coordinate scale times the original
reference product. The two endpoints are measure zero. -/
theorem eigenfunction_inner (a : ℝ) (i j : ℕ) :
    (∫ t in (0:ℝ)..1,eigenfunction a i t*eigenfunction a j t)=
      (∫ x in (0:ℝ)..1,jacobi.Jacobi.weight (jacobiIndex a) (jacobiIndex a) x*
        ((jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) i).eval x*
          (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) j).eval x))/coordinateScale a := by
  -- The substitution theorem permits the actual integrable singular endpoint weights without adding a continuity hypothesis there.
  have h := coordinate_substitution (fun x => jacobi.Jacobi.weight (jacobiIndex a) (jacobiIndex a) x*
    ((jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) i).eval x*
      (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) j).eval x))
  have he : (∫ t in (0:ℝ)..1,
      (jacobi.Jacobi.weight (jacobiIndex a) (jacobiIndex a) (coordinate t)*
        ((jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) i).eval (coordinate t)*
          (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) j).eval (coordinate t)))*coordinateSlope t)=
      ∫ t in (0:ℝ)..1,coordinateScale a*(eigenfunction a i t*eigenfunction a j t) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t hmem
    have ht : t∈Ioo (0:ℝ) 1 := by simpa only [uIoo_of_lt (by norm_num : (0:ℝ)<1)] using hmem
    have hw := coordinate_weight a ht
    unfold eigenfunction jacobi.Jacobi.angular coordinate
    change jacobi.Jacobi.weight (jacobiIndex a) (jacobiIndex a) ((1-cos (Real.pi*t))/2)*coordinateSlope t=
      coordinateScale a*(weight a t)^2 at hw
    linear_combination
      (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) i).eval ((1-cos (Real.pi*t))/2)*
      (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) j).eval ((1-cos (Real.pi*t))/2)*hw
  rw [he,intervalIntegral.integral_const_mul] at h
  exact (eq_div_iff (coordinateScale_pos a).ne').mpr (by nlinarith)

/-- Different original reference Gegenbauer eigenfunctions are genuinely orthogonal on the full unit interval.
Use: normalizes the complete reference orthogonal system used in the Gel'fand--Levitan construction.
Article: jacobi, Lemma C.1.
Proof: the exact genuine coordinate identity reduces to the already proved actual equal-parameter Jacobi orthogonality. -/
theorem eigenfunction_orthogonal {a : ℝ} (ha : -1<a) {i j : ℕ} (hij : i≠j) :
    (∫ t in (0:ℝ)..1,eigenfunction a i t*eigenfunction a j t)=0 := by
  rw [eigenfunction_inner a,jacobi.Jacobi.shiftedPolynomial_orthogonal (parameters ha).2 (parameters ha).2 hij,zero_div]

/-- The actual source reference squared norm, defined by its original integral.
Use: fixes the denominator f_n in the norming ratios and every actual GL kernel summand.
Article: jacobi, Lemma C.1.
-/
def norming (a : ℝ) (k : ℕ) : ℝ := ∫ t in (0:ℝ)..1,(eigenfunction a k t)^2

/-- The genuine reference squared norm is exactly the actual Jacobi weighted norm with the proved coordinate normalization.
Use: the exact source Gamma value follows from the independently proved Jacobi norm recurrence and Beta integral.
Article: jacobi, Lemma C.1.
Proof: set the two indices equal in the genuine original inner-product formula. -/
theorem norming_eq (a : ℝ) (k : ℕ) :
    norming a k=jacobiNorm (jacobiIndex a) (jacobiIndex a) k/coordinateScale a := by
  simpa only [norming,jacobiNorm,pow_two] using eigenfunction_inner a k k

/-- Every original reference norming constant is strictly positive, with no additional spectral assumptions.
Use: the actual GL kernel normalization and normalized reference eigenfunctions are legitimate over the complete original order range.
Article: jacobi, Lemma C.1.
Proof: the genuine Jacobi norm is positive and the exact actual coordinate normalization is positive. -/
theorem norming_pos {a : ℝ} (ha : -1<a) (k : ℕ) : 0<norming a k := by
  rw [norming_eq a]
  exact div_pos (jacobiNorm_pos (parameters ha).2 (parameters ha).2 k) (coordinateScale_pos a)

end
end jacobi.Reference
