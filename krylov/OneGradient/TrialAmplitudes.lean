import krylov.Envelope.CanonicalTrialSums
set_option autoImplicit false
/-!
Article: Lemma C.3 [s5:trial] of krylov.tex.
Use: prove the trial-error amplitude identity for the coefficients of the actual
full-memory XRFC executor, rather than for an unrelated abstract sequence.
Source: the previously proved canonical XRFC back substitution; the scalar
overshoot and undershoot comparisons are proved here directly.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Envelope krylov.Methods krylov.Reference
open scoped BigOperators

/-- The two relative-error conventions agree by the article's fractional transform.
Use: convert trial errors into chronological virtual-correction factors.
Article: main_krylov, s5:trial(a).
Proof: clear only the nonzero actual exact step and actual chosen trial. -/
theorem trial_error_transform {a t : ℝ} (ha : a≠0) (ht : t≠0) :
    (1-t/a)/(1-(1-t/a))=a/t-1 := by
  rw [show 1-(1-t/a)=t/a by ring]
  field_simp

/-- An overshooting positive trial has a virtual-correction factor strictly below one.
Use: show why an arbitrarily large positive overshoot never amplifies an older
trial defect by more than one at this iteration.
Article: main_krylov, s5:trial(a).
Proof: its absolute factor is the positive relative excess of the trial, which
is strictly smaller than one because the exact step is positive. -/
theorem overshoot_factor_lt_one {a t : ℝ} (ha : 0<a) (hat : a≤t) :
    |(a-t)/t|<1 := by
  have ht : 0<t := ha.trans_le hat
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hat) ht.le)]
  have he : -((a-t)/t)=(t-a)/t := by ring
  rw [he]
  exact (div_lt_one ht).mpr (by linarith)

/-- Undershooting by more than a factor two amplifies the old defect.
Use: identify the actual unstable scalar regime in the XRFC coefficient products.
Article: main_krylov, s5:trial(a).
Proof: the positive missed length then exceeds the entire chosen trial. -/
theorem undershoot_factor_gt_one {a t : ℝ} (ht : 0<t) (hta : t<a/2) :
    1 < |(a-t)/t| := by
  have hpos : 0<a-t := by linarith
  rw [abs_of_pos (div_pos hpos ht)]
  exact (one_lt_div ht).mpr (by linarith)

/-- The amplitudes of the genuine XRFC execution have exactly the article's
absolute chronological trial-error product.
Use: apply forgetting estimates to the actual semantic-output first variation.
Article: main_krylov, s5:trial(a).
Proof: insert the proved printed formula for the real reference execution,
then distribute absolute value through its sign, finite product and positive
square-root energy. -/
theorem xrfc_trial_coefficient_abs {n : ℕ}
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N l : ℕ)
    (hl : l<referenceAtomCount base hb g) :
    let tau := fun j => trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _ => cgOperator base) g j)
    |xrfcTrialCoefficient trial base g N l|=
      |1-tau l/CG.length (cgOperator base) g l| *
        (∏ j∈Finset.Ico (l+1) N,|(CG.length (cgOperator base) g j-tau j)/tau j|)*
          Real.sqrt (cgEnergy base g l) := by
  dsimp only
  rw [xrfcTrialCoefficient_printed trial base hb g N l hl]
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    Finset.abs_prod,abs_of_nonneg (Real.sqrt_nonneg _)]

end
end krylov.OneGradient
