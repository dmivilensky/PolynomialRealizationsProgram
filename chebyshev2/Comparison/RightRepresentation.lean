import chebyshev2.Comparison.RightFilters
import chebyshev2.Comparison.Symmetry

/-!
Article: chebyshev2, Lemma 11.
Right Representation.
Result: `chebyshev2.Calibration.Data.rightLinear_reflection` supplies the stated article
conclusion.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.Filters
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
The precise assertion is `C.rightLinear hκ q= κ*∫ y in Ioi ((C.comparisonSpeed hκ).X q), exp
(-2*(y-(C.comparisonSpeed hκ).X q))*C.comparisonDensity hκ y`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem rightLinear_integral (q : ℝ) : C.rightLinear hκ q=
    κ*∫ y in Ioi ((C.comparisonSpeed hκ).X q),
      exp (-2*(y-(C.comparisonSpeed hκ).X q))*C.comparisonDensity hκ y := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  let x := (C.comparisonSpeed hκ).X q
  have he : (∫ t in Iic (-x), exp (2*t)*reflected (C.comparisonDensity hκ) t)=
      ∫ y in Ioi x, exp (-2*y)*C.comparisonDensity hκ y := by
    have h := integral_comp_neg_Iic (-x) (fun y => exp (-2*y)*C.comparisonDensity hκ y)
    simpa only [reflected,neg_neg,mul_neg,neg_mul,neg_neg] using h
  change κ*(exp (-2*(-x))*(∫ t in Iic (-x), exp (2*t)*reflected (C.comparisonDensity hκ) t))=_
  rw [he,← integral_const_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only
  rw [← mul_assoc,← exp_add]
  congr 1
  dsimp [x]
  ring_nf

/--
Exact identity `C.rightFilter hκ s q=nonlinear s (C.comparisonDensity hκ) ((C.comparisonSpeed
hκ).X (2-q))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightFilter_reflection (s : ℝ)
    (hΓ : ∀ q ∈ Icc (0:ℝ) 2, C.Gamma (2-q)=C.Gamma q) (q : ℝ) :
    C.rightFilter hκ s q=nonlinear s (C.comparisonDensity hκ) ((C.comparisonSpeed hκ).X (2-q)) := by
  have he : reflected (C.comparisonDensity hκ)=C.comparisonDensity hκ :=
    funext (C.comparisonDensity_reflection hκ hΓ)
  unfold rightFilter
  rw [he,C.comparisonX_reflection hκ hΓ]

/--
Exact identity `C.rightLinear hκ q=linear ((C.comparisonSpeed hκ).density_integrable hκ)
((C.comparisonSpeed hκ).density_nonneg hκ) ((C.comparisonSpeed hκ).X (2-q))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 11.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem rightLinear_reflection
    (hΓ : ∀ q ∈ Icc (0:ℝ) 2, C.Gamma (2-q)=C.Gamma q) (q : ℝ) :
    C.rightLinear hκ q=linear ((C.comparisonSpeed hκ).density_integrable hκ)
      ((C.comparisonSpeed hκ).density_nonneg hκ) ((C.comparisonSpeed hκ).X (2-q)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : reflected (C.comparisonDensity hκ)=C.comparisonDensity hκ :=
    funext (C.comparisonDensity_reflection hκ hΓ)
  unfold rightLinear linear
  rw [he,(C.comparisonSpeed hκ).groundParameter_density hκ,C.comparisonX_reflection hκ hΓ]
  rfl

end
end chebyshev2.Calibration.Data
