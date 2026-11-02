import krylov.Correction.DeepChain
import krylov.Correction.DeepQuotient
import krylov.Correction.SingularFamily

/-!
Article: main_krylov, prop:deep, exact original determinant and numerator bounds.
Use: Derive the printed strict determinant signs and uniform physical
numerator and incoming-gradient estimates from the fully checked genuine
source execution, and identify its real terminal RFC quotient output.
Source: unchanged integer-expression checker soundness, exact rational
comparison and the genuine original determinant/adjugate residual identity.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

/-- The exact final-phase original source output-inventory index.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
-/
def sourceFinalIndex (i : Fin 31) : Fin (sourceOutputs 3).length :=
  ⟨i.val,by rw [sourceOutputs_length]; exact i.isLt⟩

/-- The actual determinant output is precisely the original latest-model determinant expression.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem sourceOutputs_determinant (k : Fin 4) :
    (sourceOutputs k).get (sourcePrimaryIndex k 4)=termDet (sourceModel k.val) := by
  fin_cases k <;> decide +kernel

/-- The true terminal determinant output is exactly the original four-dimensional latest-model determinant.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem sourceOutputs_determinant_last :
    (sourceOutputs 3).get (sourcePrimaryIndex 3 4)=termDet (sourceModel 3) := by decide +kernel

/-- The terminal checked squared-numerator expression is exactly the original physical adjugate-numerator pairing.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem sourceOutputs_numerator :
    (sourceOutputs 3).get (sourceFinalIndex 21)=termDot sourceNumerator sourceNumerator := by decide +kernel

/-- The terminal checked incoming-gradient expression is exactly the original actual post-search gradient pairing.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem sourceOutputs_post :
    (sourceOutputs 3).get (sourceFinalIndex 22)=termDot (sourcePost 3) (sourcePost 3) := by decide +kernel

/-- A strict exact rational scaled upper comparison implies the same bound for every genuinely enclosed real value.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem Bounds.mem_lt_rat {scale : ℕ} (hs : 0<scale) {I : Bounds} {x : ℝ} (hx : I.Mem scale x)
    (q : ℚ) (hi : I.hi*(q.den : ℤ)<(scale : ℤ)*q.num) : x<(q : ℝ) := by
  have hscale : (0 : ℝ)<scale := by exact_mod_cast hs
  have hden : (0 : ℝ)<q.den := by exact_mod_cast q.den_pos
  have hhi : (I.hi : ℝ)*q.den<(scale : ℝ)*q.num := by exact_mod_cast hi
  have hmul := mul_le_mul_of_nonneg_right hx.2 hden.le
  have hh : x*(q.den : ℝ)<q.num := by nlinarith
  simpa only [Rat.cast_def] using (lt_div_iff₀ hden).2 hh

/-- A strict exact rational scaled lower comparison implies the same bound for every genuinely enclosed real value.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem Bounds.mem_gt_rat {scale : ℕ} (hs : 0<scale) {I : Bounds} {x : ℝ} (hx : I.Mem scale x)
    (q : ℚ) (hi : (scale : ℤ)*q.num<I.lo*(q.den : ℤ)) : (q : ℝ)<x := by
  have hscale : (0 : ℝ)<scale := by exact_mod_cast hs
  have hden : (0 : ℝ)<q.den := by exact_mod_cast q.den_pos
  have hlo : (scale : ℝ)*q.num<(I.lo : ℝ)*q.den := by exact_mod_cast hi
  have hmul := mul_le_mul_of_nonneg_right hx.1 hden.le
  have hh : (q.num : ℝ)<x*(q.den : ℝ) := by nlinarith
  simpa only [Rat.cast_def] using (div_lt_iff₀ hden).2 hh

/-- The genuine original terminal latest-model determinant along the recursively evaluated true RFC source family.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
-/
def deepDeterminant (s : ℝ) : ℝ := (termDet (sourceModel 3)).value (sourceData 3 s)
/-- The genuine original physical terminal adjugate numerator along the true RFC source family.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
-/
def deepNumerator (s : ℝ) : EuclideanSpace ℝ (Fin 4) := euclideanValue sourceNumerator (sourceData 3 s)
/-- The genuine original pre-correction post-search gradient along the true RFC source family.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
-/
def deepPost (s : ℝ) : EuclideanSpace ℝ (Fin 4) := euclideanValue (sourcePost 3) (sourceData 3 s)

/-- The exact integer terminal numerator enclosure exceeds the original printed strict squared lower bound.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_numerator_checked :
    (deepScale : ℤ)*(1/(10^107) : ℚ).num<
      ((deepEnclosure 0 3).outputs (sourceFinalIndex 21)).lo*((1/(10^107) : ℚ).den : ℤ) := by decide +kernel

/-- The exact integer terminal post-search gradient enclosure satisfies the original printed strict squared upper bound.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_post_checked :
    ((deepEnclosure 0 3).outputs (sourceFinalIndex 22)).hi*((4/(10^23) : ℚ).den : ℤ)<
      (deepScale : ℤ)*(4/(10^23) : ℚ).num := by decide +kernel

/-- The exact left-endpoint integer model determinant enclosure exceeds the printed strict positive bound.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_left_checked :
    (deepScale : ℤ)*(26/(10^168) : ℚ).num<
      ((deepEnclosure 1 3).outputs (sourcePrimaryIndex 3 4)).lo*((26/(10^168) : ℚ).den : ℤ) := by decide +kernel

/-- The exact right-endpoint integer model determinant enclosure satisfies the printed strict negative bound.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_right_checked :
    ((deepEnclosure 2 3).outputs (sourcePrimaryIndex 3 4)).hi*((-75/(10^168) : ℚ).den : ℤ)<
      (deepScale : ℤ)*(-75/(10^168) : ℚ).num := by decide +kernel

/-- The genuine original physical adjugate numerator has squared norm strictly greater than the printed one-over-ten-to-the-107 bound on the whole source interval.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_numerator_square {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) :
    (1 : ℝ)/(10^107)<‖deepNumerator s‖^2 := by
  have hh := (deepEnclosure 0 3).enclosed deepScale_pos (deep_all_enclosed 0 hs _) (sourceFinalIndex 21)
  rw [sourceOutputs_numerator,termDot_inner,real_inner_self_eq_norm_sq] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  simpa only [deepNumerator,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg,Fin.val_ofNat,Nat.reduceMod] using Bounds.mem_gt_rat deepScale_pos hh (1/(10^107)) deep_numerator_checked

/-- The genuine original post-search gradient has squared norm strictly below the printed four-times-ten-to-the-minus-23 bound throughout the interval.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_post_square {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) :
    ‖deepPost s‖^2<(4 : ℝ)/(10^23) := by
  have hh := (deepEnclosure 0 3).enclosed deepScale_pos (deep_all_enclosed 0 hs _) (sourceFinalIndex 22)
  rw [sourceOutputs_post,termDot_inner,real_inner_self_eq_norm_sq] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  simpa only [deepPost,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg,Fin.val_ofNat,Nat.reduceMod] using Bounds.mem_lt_rat deepScale_pos hh (4/(10^23)) deep_post_checked

/-- The true original terminal model determinant at the left dyadic endpoint satisfies the printed strict positive sign estimate.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_determinant_left : (26 : ℝ)/(10^168)<deepDeterminant deepLeft := by
  have hs : (deepLeft : ℝ)∈Set.Icc (deepDomainLeft 1 : ℝ) (deepDomainRight 1 : ℝ) := ⟨le_rfl,le_rfl⟩
  have hh := (deepEnclosure 1 3).enclosed deepScale_pos (deep_all_enclosed 1 hs _) (sourcePrimaryIndex 3 4)
  rw [sourceOutputs_determinant_last] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  simpa only [deepDeterminant,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg,Fin.val_ofNat,Nat.reduceMod] using Bounds.mem_gt_rat deepScale_pos hh (26/(10^168)) deep_left_checked

/-- The true original terminal model determinant at the right dyadic endpoint satisfies the printed strict negative sign estimate.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_determinant_right : deepDeterminant deepRight<(-75 : ℝ)/(10^168) := by
  have hs : (deepRight : ℝ)∈Set.Icc (deepDomainLeft 2 : ℝ) (deepDomainRight 2 : ℝ) := ⟨le_rfl,le_rfl⟩
  have hh := (deepEnclosure 2 3).enclosed deepScale_pos (deep_all_enclosed 2 hs _) (sourcePrimaryIndex 3 4)
  rw [sourceOutputs_determinant_last] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  simpa only [deepDeterminant,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg,Fin.val_ofNat,Nat.reduceMod] using Bounds.mem_lt_rat deepScale_pos hh (-75/(10^168)) deep_right_checked

/-- The genuine original terminal model determinant is continuous on the entire true dyadic source interval.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_determinant_continuous : ContinuousOn deepDeterminant (Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) := by
  have hh := (deepEnclosure 0 3).continuousOn deepScale_pos (fun _ hs => deep_all_enclosed 0 hs _) (deep_all_continuousOn 0 3) (sourcePrimaryIndex 3 4)
  rw [sourceOutputs_determinant_last] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  dsimp only [deepDomainLeft,deepDomainRight] at hh
  simp only [ite_eq_right (by decide : (0 : Fin 3)≠2),ite_eq_right (by decide : (0 : Fin 3)≠1)] at hh
  exact hh

/-- The genuine terminal RFC gradient equals exactly the printed post-search gradient minus its actual physical adjugate numerator divided by its real latest-model determinant.
Use: Complete the exact source-specific original RFC singular-model certificate.
Article: main_krylov, prop:deep, printed original physical inequalities.
Proof: Use the accepted exact source enclosure and independent source expression identity.
-/
theorem deep_actual_output {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) :
    probedGradient (rfcMethod fullMemory 1) (deepScenario s).probeOracle
      ((deepScenario s).correctionOracle 3) deepInitial 4=
      deepPost s-(deepDeterminant s)⁻¹ • deepNumerator s := by
  have hh := (deep_all_realizes 0 hs 4 (by omega)).1
  change euclideanValue (sourceInputPrefix 4).gradient (sourceData 4 s)=_ at hh
  simp only [sourceData_probes,sourceData_corrections,sourceInitial_value] at hh
  rw [sourceData_gradient] at hh
  exact hh.symm.trans (source_phase_last_quotient (sourceData 3 s))

end
end krylov.Correction.Certificate
