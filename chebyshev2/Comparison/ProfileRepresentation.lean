import chebyshev2.Comparison.ProfileJost

/-!
Article: chebyshev2, Lemma 11.
The anticausal integral formula for arbitrary Definition 10 profiles.
Result: `chebyshev2.Comparison.Profile.rightLinear_integral` supplies the stated article
conclusion.
-/
namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.Filters
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : chebyshev2.Comparison.Profile κ) (hκ : 0 < κ)

/--
The precise assertion is `P.rightLinear hκ q= κ*∫ y in Ioi ((P.speedData hκ).X q), exp
(-2*(y-(P.speedData hκ).X q))*P.density hκ y`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 11.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem rightLinear_integral (q : ℝ) : P.rightLinear hκ q=
    κ*∫ y in Ioi ((P.speedData hκ).X q),
      exp (-2*(y-(P.speedData hκ).X q))*P.density hκ y := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  let x := (P.speedData hκ).X q
  have he : (∫ t in Iic (-x), exp (2*t)*reflected (P.density hκ) t)=
      ∫ y in Ioi x, exp (-2*y)*P.density hκ y := by
    have h := integral_comp_neg_Iic (-x) (fun y => exp (-2*y)*P.density hκ y)
    simpa only [reflected,neg_neg,mul_neg,neg_mul,neg_neg] using h
  change κ*(exp (-2*(-x))*(∫ t in Iic (-x), exp (2*t)*reflected (P.density hκ) t))=_
  rw [he,← integral_const_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only
  rw [← mul_assoc,← exp_add]
  congr 1
  dsimp [x]
  ring_nf

end
end chebyshev2.Comparison.Profile
