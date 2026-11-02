import krylov.Correction.DeepFeatures
import krylov.LinearAlgebra.LeadingPosDef

/-!
Article: main_krylov, prop:deep, original auxiliary numerical assertions.
Use: Certify positive source line-search lengths, strict printed squared
Frobenius defect bounds, leading minors and the actual terminal basis rank.
Source: original source expressions and unchanged integer checker; the
penultimate second leading minor is independently decoded from the already
checked shared arithmetic graph, with no extra numerical premise.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

/-- The genuine second leading determinant of the original third correction model.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
-/
def sourcePenultimateLeading : Term := termDet ((sourceModel 2).submatrix
  (Fin.castLE (by decide : 2≤3)) (Fin.castLE (by decide : 2≤3)))
/-- The exact integer enclosure of the original penultimate second leading determinant.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
-/
def deepPenultimateLeadingBounds : Bounds := ⟨(17055537461583019626042935779009634897713023044156830201049373516021253622484001886840073407738160313074312889983554422377204804992373307739319355643351903651970668404742797172829133940537763564451810562925714949678996142711832292348254961162157057522735785135335447825269394365059798554441828709635580991868425128546350476917238),(17055537461583019626042935779009634897713023044156830201049373516021253622484001886840073407738160313074312889983554422377204805021563177930613873198034421207905110514071047284078446409849661322656613007897172980818212267736039809053118704832803700937136754913106359554072586244633995952457386804614881028820095437507296663372788)⟩

/-- The checked original arithmetic stack contains exactly the independently specified penultimate leading determinant.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_penultimate_leading_decoded :
    codeExpressionCheck deepStage2Operations 124 sourcePenultimateLeading=true := by decide +kernel

/-- The checked original arithmetic stack gives precisely the claimed penultimate leading-determinant interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_penultimate_leading_lookup :
    (programBounds deepStage2Interval.inputs
      (annotate deepStage2Operations deepStage2Interval.bounds))[124]?=some deepPenultimateLeadingBounds := by decide +kernel

/-- The genuine penultimate second leading principal determinant is strictly positive throughout the entire source interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_penultimate_leading_positive {s : ℝ}
    (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) :
    0<sourcePenultimateLeading.value (sourceData 2 s) := by
  -- Decode the genuine leading determinant from the already accepted original block before extracting its strictly positive real lower bound.
  have hx := deep_all_enclosed 0 hs (2 : Fin 4)
  simp only [show (2 : Fin 4).val=2 from rfl] at hx
  have hh := source_enclosed deepScale_pos (annotate deepStage2Operations deepStage2Interval.bounds)
    hx deepStage2Interval.accepted
    (expressionCheck_of_code deepStage2Interval.length_eq deep_penultimate_leading_decoded)
    deep_penultimate_leading_lookup
  exact Bounds.mem_pos deepScale_pos hh (by decide +kernel)

/-- The checked primary source output is exactly the original true line-search length expression.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem sourceOutputs_alpha (k : Fin 4) :
    (sourceOutputs k).get (sourcePrimaryIndex k 0)=
      termLineLength (sourceInputPrefix k.val).gradient (sourceDirection k.val) (sourceImage k.val) := by
  fin_cases k <;> decide +kernel

/-- The checked augmented defect output is exactly the genuine original rational squared-defect expression.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem sourceOutputs_augDefect (k : Fin 4) :
    (sourceOutputs k).get (sourcePrimaryIndex k 2)=
      termDefectSquare (sourceAugSteps k.val) (sourceAugImages k.val) := by
  fin_cases k <;> decide +kernel

/-- The three terminal leading-minor outputs are precisely the original latest-model principal determinants.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem sourceOutputs_leading (i : Fin 3) :
    (sourceOutputs 3).get (sourceFinalIndex ⟨28+i.val,by have := i.isLt; omega⟩)=
      sourceLeading (i.val+1) (by have := i.isLt; omega) := by
  fin_cases i <;> decide +kernel

/-- The terminal basis output is precisely the original genuine augmented-direction determinant.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem sourceOutputs_basis : (sourceOutputs 3).get (sourceFinalIndex 23)=termDet sourceBasis := by decide +kernel

/-- Every original source line-search length has a strictly positive checked integer lower bound.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_alpha_checked (k : Fin 4) : 0<((deepEnclosure 0 k).outputs (sourcePrimaryIndex k 0)).lo := by
  fin_cases k <;> decide +kernel

/-- Every original augmented squared defect satisfies the strict printed one-millionth upper bound in the exact integer checker.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_aug_defect_checked (k : Fin 4) :
    ((deepEnclosure 0 k).outputs (sourcePrimaryIndex k 2)).hi*((1/(10^6) : ℚ).den : ℤ)<
      (deepScale : ℤ)*(1/(10^6) : ℚ).num := by
  fin_cases k <;> decide +kernel

/-- Every original preterminal correction-model determinant has a strictly positive checked integer lower bound.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_preterminal_det_checked (k : Fin 3) :
    0<((deepEnclosure 0 k.castSucc).outputs (sourcePrimaryIndex k.castSucc 4)).lo := by
  fin_cases k <;> decide +kernel

/-- The first three original terminal leading principal determinants have strictly positive checked integer lower bounds.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_leading_checked (i : Fin 3) :
    0<((deepEnclosure 0 3).outputs (sourceFinalIndex ⟨28+i.val,by have := i.isLt; omega⟩)).lo := by
  fin_cases i <;> decide +kernel

/-- The genuine original terminal augmented basis determinant has a strictly positive checked lower bound.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_basis_checked : 0<((deepEnclosure 0 3).outputs (sourceFinalIndex 23)).lo := by decide +kernel

/-- Every actual original source line-search length is strictly positive on the whole source interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_alpha_positive {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 4) :
    0<(termLineLength (sourceInputPrefix k.val).gradient (sourceDirection k.val) (sourceImage k.val)).value (sourceData k.val s) := by
  have hh := (deepEnclosure 0 k).enclosed deepScale_pos (deep_all_enclosed 0 hs k) (sourcePrimaryIndex k 0)
  rw [sourceOutputs_alpha] at hh
  exact Bounds.mem_pos deepScale_pos hh (deep_alpha_checked k)

/-- Every genuine original augmented source squared defect satisfies the printed strict one-millionth bound on the whole interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_aug_defect_small {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 4) :
    (termDefectSquare (sourceAugSteps k.val) (sourceAugImages k.val)).value (sourceData k.val s)<(1 : ℝ)/(10^6) := by
  have hh := (deepEnclosure 0 k).enclosed deepScale_pos (deep_all_enclosed 0 hs k) (sourcePrimaryIndex k 2)
  rw [sourceOutputs_augDefect] at hh
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
    Bounds.mem_lt_rat deepScale_pos hh (1/(10^6)) (deep_aug_defect_checked k)

/-- Every genuine original preterminal correction-model determinant is strictly positive throughout the source interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_preterminal_det_positive {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 3) :
    0<(termDet (sourceModel k.val)).value (sourceData k.val s) := by
  have hh := (deepEnclosure 0 k.castSucc).enclosed deepScale_pos (deep_all_enclosed 0 hs k.castSucc) (sourcePrimaryIndex k.castSucc 4)
  rw [sourceOutputs_determinant] at hh
  exact Bounds.mem_pos deepScale_pos hh (deep_preterminal_det_checked k)

/-- The first three actual terminal latest-model leading principal determinants are strictly positive throughout the source interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_leading_positive {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (i : Fin 3) :
    0<(sourceLeading (i.val+1) (by have := i.isLt; omega)).value (sourceData 3 s) := by
  have hh := (deepEnclosure 0 3).enclosed deepScale_pos (deep_all_enclosed 0 hs _) (sourceFinalIndex ⟨28+i.val,by have := i.isLt; omega⟩)
  rw [sourceOutputs_leading] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  exact Bounds.mem_pos deepScale_pos hh (deep_leading_checked i)

/-- The genuine original terminal augmented direction matrix is nonsingular throughout the source interval.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_basis_nonsingular {s : ℝ} (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) :
    (matrixValue sourceBasis (sourceData 3 s)).det≠0 := by
  have hh := (deepEnclosure 0 3).enclosed deepScale_pos (deep_all_enclosed 0 hs _) (sourceFinalIndex 23)
  rw [sourceOutputs_basis,termDet_value] at hh
  simp only [show (3 : Fin 4).val=3 from rfl] at hh
  exact (Bounds.mem_pos deepScale_pos hh deep_basis_checked).ne'

/-- Every interpreted original latest-probe correction model is genuinely real Hermitian.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem sourceModel_hermitian (k : ℕ) (x : ℕ → ℝ) : (matrixValue (sourceModel k) x).IsHermitian := by
  rw [sourceModel,termPairModel_value]
  exact pairModel_isHermitian _ _

/-- Every genuine original source correction model has a strictly positive first leading principal determinant.
Use: Cover the original printed auxiliary numerical assertions on the actual source family.
Article: main_krylov, prop:deep, complete auxiliary source certificate.
Proof: Use the independently decoded exact original source expression and fully checked real enclosure.
-/
theorem deep_leading_one_positive {s : ℝ}
    (hs : s∈Set.Icc (deepLeft : ℝ) (deepRight : ℝ)) (k : Fin 4) :
    0<(leadingBlock (matrixValue (sourceModel k.val) (sourceData k.val s)) 1 (by omega)).det := by
  have hh := (deepEnclosure 0 k).enclosed deepScale_pos (deep_all_enclosed 0 hs k) (sourceEnergyIndex k 0)
  rw [sourceOutputs_energy] at hh
  have hp := Bounds.mem_pos deepScale_pos hh (deep_energy_checked 0 k 0)
  rw [Matrix.det_fin_one]
  exact hp

end
end krylov.Correction.Certificate
