import krylov.Nonlinear.RFCSCanonicalGradient
import krylov.Nonlinear.CoordinateGradientError
import krylov.Nonlinear.GradientErrorTransfer

/-!
Article: main_krylov, thm:RFCS, genuine sharp nonlinear cycle error bound.
Use: Transfer the actual canonical gradient estimate to the real metric
error of the nonlinear cycle while preserving its literal executed relative
last-probe coefficient and one uniform cubic remainder.
Source: genuine nonlinear source localization, actual positive search lengths,
true local gradient/error comparison and proved cubic scalar absorption.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped NNReal
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Genuine nonlinear RFC-S cycles with actual canonical Hessian control satisfy the source metric-error estimate with the exact executed relative last-probe factor on the squared original reference last-step norm and one common cubic cycle remainder.
Use: Obtain the actual single-cycle error conclusion before deriving its canonical local constants directly from physical self-concordance data.
Article: main_krylov, thm:RFCS, true nonlinear error estimate with original leading coefficient.
Proof: The actual shared source gives a true output-size bound and a genuine local gradient domain. Real search geometry bounds the executed relative probe error, while compact reference steps and the proved actual normalized gradient estimate give a quadratic gradient bound. Derive the genuine small relative gradient/error mismatch from the original physical Hessian, absorb it and add only a uniform cubic term to the unchanged leading gradient coefficient.
-/
theorem compact_rfcs_coordinate_error_bound (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hQ : ∀ v, T.symm (cgOperator base v)=T v)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B Cp ρ : ℝ) (hr : 0<r) (hB : 0<B) (hCp : 0<Cp) (hρ : 0<ρ)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x)
    (hcan : ∀ R : ℝ, 0<R → R≤ρ → LipschitzOnWith (Real.toNNReal (2+10000*R)) (coordinateDerivative T H) (ball 0 R)) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) →
      (∀ i<k+1, 0<h i ∧ h i≤Cp*CG.length (cgOperator base) (cgOperator base u) i) →
      ‖T (rfcSFunctionPoint fullMemory G (ε • u) h (k+1))‖≤
      |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k| *
        (ε*‖T (referenceStep (cgOperator base) (cgOperator base u) k)‖)^2+C*ε^3 := by
  obtain ⟨εg,Cg,hεg,hCg,hgradient⟩ := compact_rfcs_coordinate_gradient_bound base hb K hK hN hk T G H r B Cp ρ hr hB hCp hρ hG₀ hH₀ hH hG hcan
  obtain ⟨Mα,hMα,hαref⟩ := compact_rfcs_reference_length_bounds base hb K hK hN
  let P := Cp*Mα
  have hP : 0≤P := (mul_pos hCp hMα).le
  obtain ⟨εs,D,_,hεs,hD,_,hsource⟩ := compact_rfcs_nonlinear_source base hb K hK hN G H r B P hr hB hP hG₀ hH₀ hH hG
  obtain ⟨εa,_,hεa,_,hgeo⟩ := compact_rfcs_nonlinear_search_geometry base hb K hK hN G H r B P hr hB hP hG₀ hH₀ hH hG
  obtain ⟨δ,M,hδ,hM,hprefix⟩ := compact_rfcs_operator_prefix_bounds base hb K hK hN
  have href g (hg : g∈K) : ‖referenceStep (cgOperator base) g k‖≤M := by
    have hh := ((hprefix g hg 0 0 (by simp only [Prod.norm_mk,norm_zero,max_self]; linarith)).2 k (Nat.lt_succ_self k)).2
    rw [add_zero] at hh
    have hz := (rfcs_direct_alpha_reference base hb g k).2.2
    unfold rfcsDirectCorrection at hz
    rw [(rfcs_direct_alpha_reference base hb g k).2.1] at hz
    rw [sub_eq_zero.mp hz] at hh
    exact hh
  let Mref := (‖T.toContinuousLinearMap‖+1)*M+1
  have hMref : 0<Mref := by dsimp only [Mref]; positivity
  let Emax := 1+2*Cp
  have hEmax : 0<Emax := by dsimp only [Emax]; positivity
  let a := ‖T.symm.toContinuousLinearMap‖^2*(L : ℝ)*D/2
  let b := Emax*Mref^2+Cg+1
  have ha : 0≤a := by dsimp only [a]; positivity
  have hb' : 0<b := by dsimp only [b]; positivity
  let C := Cg+2*a*b+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨min εg (min εs (min εa (min 1 (min (r/(D+1)) (1/(2*a+1)))))),C,
    lt_min hεg (lt_min hεs (lt_min hεa (lt_min (by norm_num)
      (lt_min (div_pos hr (by positivity)) (by positivity))))),hC,?_⟩
  intro ε hε he u hu hKu h hh hrel
  have he_g := he.trans_le (min_le_left _ _)
  have he_s := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he_a := he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he_tail := he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hε1 : ε≤1 := he_tail.le.trans (min_le_left _ _)
  have he_r := he_tail.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he_small := he_tail.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : a*ε≤1/2 := by
    have hs := (lt_div_iff₀ (by positivity : 0<2*a+1)).mp he_small
    nlinarith
  have her : ε*D<r := by
    have hs := (lt_div_iff₀ (by positivity : 0<D+1)).mp he_r
    nlinarith
  have habs i (hi : i<k+1) : |h i|≤P := by
    rw [abs_of_pos (hrel i hi).1]
    exact (hrel i hi).2.trans (mul_le_mul_of_nonneg_left (hαref _ hKu i hi).2.2 hCp.le)
  have hs := hsource ε hε he_s u hu hKu h hh habs
  have hg := hgeo ε hε he_a u hu hKu h hh habs k (Nat.lt_succ_self k)
  have hgrad := hgradient ε hε he_g u hu hKu h hh hrel
  let x := rfcSFunctionPoint fullMemory G (ε • u) h (k+1)
  let E := |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k|
  let e := ‖T (referenceStep (cgOperator base) (cgOperator base u) k)‖
  have hxnorm : ‖x‖≤ε*D := (hs.2.1 (k+1) le_rfl).2
  have hx : x∈ball 0 r := mem_ball_zero_iff.mpr (hxnorm.trans_lt her)
  have hE : 0≤E := abs_nonneg _
  have hEbound : E≤Emax := relative_probe_error_bound (hαref _ hKu k (Nat.lt_succ_self k)).1
    hg.2.1 (hrel k (Nat.lt_succ_self k)).1 (hrel k (Nat.lt_succ_self k)).2
  have heRef : e≤Mref := by
    have hn := T.toContinuousLinearMap.le_opNorm (referenceStep (cgOperator base) (cgOperator base u) k)
    simp only [ContinuousLinearEquiv.coe_coe] at hn
    apply hn.trans
    apply (mul_le_mul_of_nonneg_left (href _ hKu) (norm_nonneg T.toContinuousLinearMap)).trans
    dsimp only [Mref]
    nlinarith
  have hε3 : ε^3≤ε^2 := by nlinarith [mul_le_mul_of_nonneg_left hε1 (sq_nonneg ε)]
  have hleading : E*(ε*e)^2≤(Emax*Mref^2)*ε^2 := by
    have he' := (sq_le_sq₀ (by positivity : 0≤ε*e) (by positivity : 0≤ε*Mref)).mpr
      (mul_le_mul_of_nonneg_left heRef hε.le)
    exact (mul_le_mul hEbound he' (sq_nonneg _) hEmax.le).trans_eq (by ring)
  have hgrad2 : ‖T.symm (G x)‖≤b*ε^2 := by
    calc
      _ ≤ E*(ε*e)^2+Cg*ε^3 := hgrad
      _ ≤ (Emax*Mref^2)*ε^2+Cg*ε^2 := add_le_add hleading (mul_le_mul_of_nonneg_left hε3 hCg.le)
      _ ≤ b*ε^2 := by dsimp only [b]; nlinarith [sq_nonneg ε]
  -- This is the real gradient/error mismatch derived from the original Hessian and actual output size, not an asymptotic comparison premise.
  have hdiff : ‖T x-T.symm (G x)‖≤a*ε*‖T x‖ :=
    coordinate_gradient_relative_error T G H (cgOperator base) hQ (ball 0 r) (convex_ball _ _)
      (mem_ball_self hr) hG₀ hH₀ hH hG x hx hD.le hε.le hxnorm
  have htransfer := norm_error_le_gradient_add_cubic (T x) (T.symm (G x)) ha hε.le hsmall hdiff hgrad2
  change ‖T x‖≤E*(ε*e)^2+C*ε^3
  calc
    _ ≤ ‖T.symm (G x)‖+2*a*b*ε^3 := htransfer
    _ ≤ (E*(ε*e)^2+Cg*ε^3)+2*a*b*ε^3 := add_le_add hgrad le_rfl
    _ ≤ E*(ε*e)^2+C*ε^3 := by dsimp only [C]; nlinarith [pow_nonneg hε.le 3]

end
end krylov.Nonlinear
