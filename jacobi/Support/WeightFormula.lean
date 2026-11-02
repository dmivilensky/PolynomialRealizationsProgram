import jacobi.Support.WeightReflection
import jacobi.Finite.CosineLatticeRatio

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The actual canonical probabilities of the natural and corrected chains
have the printed sine-product formula. Their adjacent ratios follow from
the genuine characteristic derivatives and the exact truncation period.
All statements use the existing spectral measures of the actual matrices.
Use: naturalMeasure_adjacent_ratio and naturalMeasure_weight_formula give the exact original probabilities, whose asymptotics enter the target/support Gram comparison.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference jacobi.Finite

/-- The original adjacent sine-cosine factor in the support probability formula.
Use: naturalMeasure_adjacent_ratio and naturalMeasure_weight_formula give the exact original probabilities, whose asymptotics enter the target/support Gram comparison.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def weightIncrement (a b : ℝ) (n j : ℕ) : ℝ :=
  sin (((j:ℝ)+2*gamma a)*step a b n/2)*
    cos (((j:ℝ)+gamma a+gamma b)*step a b n/2)/
      (sin (((j:ℝ)+1)*step a b n/2)*
        cos (((j:ℝ)+1+gamma a-gamma b)*step a b n/2))

/-- The original unnormalized sine-product support probability.
Use: naturalMeasure_weight_formula identifies it with the actual spectral probability after one common positive normalization.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def weightFactor (a b : ℝ) (n k : ℕ) : ℝ :=
  sin (jacobi.Jacobi.modelAngle a b n k)*∏j∈Finset.range k,weightIncrement a b n j

/-- The two endpoint sine factors in the characteristic-gap ratio are exactly the original cosine factors.
Use: naturalMeasure_adjacent_ratio simplifies the exact characteristic derivative ratio using the actual finite period, with no asymptotic replacement.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the sum-angle endpoint is pi/2 plus its printed shift; the difference-angle endpoint is pi/2 minus its shift. Apply the exact sine quarter-period identities. -/
theorem weight_period_factors {a b : ℝ} (ha:-1<a) (hb:-1<b) (n k : ℕ) :
    sin (((k:ℝ)+n+1+2*gamma a)*step a b (n+1)/2)=
      cos (((k:ℝ)+1+gamma a-gamma b)*step a b (n+1)/2) ∧
    sin (((n:ℝ)-k)*step a b (n+1)/2)=
      cos (((k:ℝ)+gamma a+gamma b)*step a b (n+1)/2) := by
  have hper := frequency_mul_step ha hb (show 0<n+1 by omega)
  rw [frequency_gamma] at hper
  push_cast at hper
  constructor
  · rw [show ((k:ℝ)+n+1+2*gamma a)*step a b (n+1)/2=
        (((k:ℝ)+1+gamma a-gamma b)*step a b (n+1)/2)+π/2 by nlinarith only [hper],sin_add_pi_div_two]
  · rw [show ((n:ℝ)-k)*step a b (n+1)/2=
        π/2-(((k:ℝ)+gamma a+gamma b)*step a b (n+1)/2) by nlinarith only [hper],sin_pi_div_two_sub]

/-- Adjacent actual original support probabilities have precisely the printed sine-product ratio.
Use: naturalMeasure_weight_formula and fixedWeight_ratio_limit concern the original support spectral weights rather than a separately defined comparison sequence.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: cancel the common positive normalization in the actual reciprocal-characteristic-derivative probabilities. Factor their original cosine gaps and telescope both sine products. The exact original period converts the two terminal sines into the printed cosines. -/
theorem naturalMeasure_adjacent_ratio {a b : ℝ} (ha:-1<a) (hb:-1<b)
    {n k : ℕ} (hk:k<n) :
    (naturalMeasure a b ha hb n).weight ⟨k+1,by omega⟩/
      (naturalMeasure a b ha hb n).weight ⟨k,by omega⟩=
      weightIncrement a b (n+1) k*
        (sin (jacobi.Jacobi.modelAngle a b (n+1) (k+1))/
          sin (jacobi.Jacobi.modelAngle a b (n+1) k)) := by
  -- First retain precisely the original canonical derivative normalization.
  let S := naturalNodes a b ha hb (n+1)
  let i : Fin (n+1) := ⟨k,by omega⟩
  let j : Fin (n+1) := ⟨k+1,by omega⟩
  have hw : (naturalMeasure a b ha hb n).weight j/(naturalMeasure a b ha hb n).weight i=
      |S.polynomial.derivative.eval (S.value i)|/|S.polynomial.derivative.eval (S.value j)| := by
    change (|S.polynomial.derivative.eval (S.value j)|⁻¹/S.derivativeNormalizer)/
      (|S.polynomial.derivative.eval (S.value i)|⁻¹/S.derivativeNormalizer)=_
    field_simp [S.derivativeNormalizer_pos.ne',abs_pos.mpr (S.derivative_ne_zero i) |>.ne',
      abs_pos.mpr (S.derivative_ne_zero j) |>.ne']
  rw [hw]
  change |(naturalNodes a b ha hb (n+1)).polynomial.derivative.eval (naturalNode a b (n+1) i)|/
    |(naturalNodes a b ha hb (n+1)).polynomial.derivative.eval (naturalNode a b (n+1) j)|=_
  rw [naturalDerivative_product,naturalDerivative_product,Finset.abs_prod,Finset.abs_prod]
  change (∏l∈Finset.univ.erase i,|naturalNode a b (n+1) k-naturalNode a b (n+1) l|)/
    (∏l∈Finset.univ.erase j,|naturalNode a b (n+1) (k+1)-naturalNode a b (n+1) l|)=_
  rw [fin_punctured_product (fun l:ℕ => |naturalNode a b (n+1) k-naturalNode a b (n+1) l|) i,
    fin_punctured_product (fun l:ℕ => |naturalNode a b (n+1) (k+1)-naturalNode a b (n+1) l|) j]
  have hangle := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb (show n<n+1 by omega)).1
  rw [modelAngle_step] at hangle
  have hg := (parameter_pos ha hb).1
  have hratio := cosine_lattice_derivative_ratio (step_pos ha hb (show 0<n+1 by omega)) hg hangle.2 hk
  simp only [naturalNode,modelAngle_step]
  rw [hratio,(weight_period_factors ha hb n k).1,(weight_period_factors ha hb n k).2]
  simp only [weightIncrement,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Every support sine-cosine increment actually used between adjacent nodes is strictly positive.
Use: estimates for the original finite products may take logarithms and divide by the true positive factors, including near either endpoint.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the exact ratio is a quotient of the genuine positive spectral probabilities. Both original node angles have positive sine, so solving that ratio for xi_j proves its strict positivity. -/
theorem weightIncrement_pos {a b : ℝ} (ha:-1<a) (hb:-1<b) {n k : ℕ} (hk:k<n) :
    0<weightIncrement a b (n+1) k := by
  have hi := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb (show k<n+1 by omega)).1
  have hj := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb (show k+1<n+1 by omega)).1
  have hsin := div_pos (sin_pos_of_pos_of_lt_pi hj.1 hj.2) (sin_pos_of_pos_of_lt_pi hi.1 hi.2)
  have hr := naturalMeasure_adjacent_ratio ha hb hk
  have hw := div_pos ((naturalMeasure a b ha hb n).positive ⟨k+1,by omega⟩)
    ((naturalMeasure a b ha hb n).positive ⟨k,by omega⟩)
  rw [hr] at hw
  exact (mul_pos_iff_of_pos_right hsin).mp hw

/-- The actual original support weights have the complete printed sine-product formula with one common positive normalization.
Use: fixed-index weight asymptotics, global weight bounds and the target/support Gram limit use the original spectral probabilities through this exact expression.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the first actual probability fixes a positive common factor. Induct on the unchanged original spectral index using the exact adjacent ratio; its denominator sine is positive. The corrected measure retains exactly the same original probabilities. -/
theorem naturalMeasure_weight_formula {a b : ℝ} (ha:-1<a) (hb:-1<b) (n : ℕ) :
    ∃Z:ℝ,0<Z ∧ ∀k:Fin (n+1),
      (naturalMeasure a b ha hb n).weight k=Z⁻¹*weightFactor a b (n+1) k ∧
      (supportMeasure a b ha hb n).weight k=Z⁻¹*weightFactor a b (n+1) k := by
  -- Use the actual probability at the first node to fix the normalization, rather than choosing a second measure.
  let W := naturalMeasure a b ha hb n
  let s (k:ℕ) := sin (jacobi.Jacobi.modelAngle a b (n+1) k)
  have hs (k:ℕ) (hk:k≤n) : 0<s k := by
    have h := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb (show k<n+1 by omega)).1
    exact sin_pos_of_pos_of_lt_pi h.1 h.2
  have hrec (k:ℕ) (hk:k≤n) : W.weight ⟨k,by omega⟩=
      W.weight 0/s 0*weightFactor a b (n+1) k := by
    induction k with
    | zero => simp [weightFactor,s,hs 0 (by omega) |>.ne']
    | succ k ih =>
      have hk' : k<n := by omega
      have hr := (div_eq_iff (W.positive ⟨k,by omega⟩).ne').mp (naturalMeasure_adjacent_ratio ha hb hk')
      rw [hr,ih (by omega)]
      simp only [weightFactor,Finset.prod_range_succ]
      change (weightIncrement a b (n+1) k*(s (k+1)/s k))*
        (W.weight 0/s 0*(s k*∏j∈Finset.range k,weightIncrement a b (n+1) j))=_
      field_simp [(hs k (by omega)).ne']
      ring
  refine ⟨s 0/W.weight 0,div_pos (hs 0 (by omega)) (W.positive 0),?_⟩
  intro k
  have h := hrec k (by omega)
  constructor
  · simpa only [inv_div] using h
  · change W.weight k=_
    simpa only [inv_div] using h

end
end jacobi.Support
