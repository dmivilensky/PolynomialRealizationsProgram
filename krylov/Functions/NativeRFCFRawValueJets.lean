import krylov.Functions.NativeRFCFPhysicalTransfer

/-!
Article: main_krylov, prop:Fcycle(i), actual raw-coordinate value-model jets.
Use: the genuine chronological scalar jet is reversed and divided by the
actual current line scale squared. Its coordinate change has its own proved
first jet, uniformly on compact true nondegenerate reference families.
Source: original native source tube, analytic CG line quotient, genuine scalar
value defects and the exact diagonal spectral-norm product estimate.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The genuine reference value-model diagonal in the original raw newest-first basis.
Article: main_krylov, prop:Fcycle(i), true third-derivative model coefficient. -/
def rfcFReferenceRawValueChange
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Matrix.diagonal (fun i =>
    ((1/2 : ℝ)*inner ℝ (D (referenceStep (cgOperator base) (cgOperator base u) i.rev.val)
      (referenceStep (cgOperator base) (cgOperator base u) i.rev.val))
      (referenceStep (cgOperator base) (cgOperator base u) i.rev.val)) *
    ((Fin.cons (CG.length (cgOperator base) (cgOperator base u) k) (fun _ : Fin k => (1 : ℝ)) : Fin (k+1) → ℝ) i)⁻¹^2)

/-- The actual original native line scale has a genuine compact-uniform inverse-square first jet.
Article: main_krylov, prop:Fcycle(i), true scalar coordinate normalization. -/
theorem nativeRFCF_line_inverse_square
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ C M : ℝ, 0<ε₀ ∧ 0<C ∧ 0<M ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let α := rfcFActualLineScale T f G H r (ε • u) k
      α≠0 ∧ |α⁻¹^2|≤M ∧
        |α⁻¹^2-(CG.length (cgOperator base) (cgOperator base u) k)⁻¹^2|≤C*ε := by
  obtain ⟨δ,Ca,Ma,hδ,hCa,hMa,ha⟩ := compact_rfc_line_inverse_square base hb K hK hpre
  obtain ⟨ep,M,D,C,S,hep,_,_,_,hS,hinput⟩ := nativeRFC_physical_source_tube base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R δ hR hδ
  refine ⟨ep,Ca*S,Ma,hep,mul_pos hCa hS,hMa,?_⟩
  intro ε hε he u hu hKu
  obtain ⟨_,Θ,hA,_,hhistory,ht,hsmall,_⟩ := hinput ε hε he u hu hKu
  let gn := ε⁻¹ • G (ε • u)
  let v := gn-cgOperator base u
  have hv : cgOperator base u+v=gn := by dsimp only [v]; abel
  have hscaleG : G (ε • u)=ε • gn := by
    dsimp only [gn]
    rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hα : rfcFActualLineScale T f G H r (ε • u) k=rfcPhysicalLineScale base (gn,Θ) := by
    dsimp only [rfcFActualLineScale]
    rw [←hA k le_rfl,hhistory k (by omega)]
    change rfcPhysicalLineScale base (G (ε • u),Θ)=_
    rw [hscaleG,rfcPhysicalLineScale_scalar base gn Θ ε hε.ne']
  have hh := ha (cgOperator base u) hKu v Θ hsmall
  rw [hv] at hh
  rw [hα]
  exact ⟨hh.1,hh.2.1,hh.2.2.trans ((mul_le_mul_of_nonneg_left ht hCa.le).trans_eq (by ring))⟩

/-- Actual scalar diagonal and actual line-coordinate errors pass to the true raw observed matrix without losing their orders.
Article: main_krylov, prop:Fcycle(i), genuine matrix coordinate transfer. -/
theorem rfcF_raw_value_jet_bound
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r ε α J M B V : ℝ) (u : EuclideanSpace ℝ (Fin (k+1)))
    (hε : 0≤ε) (hJ : 0≤J) (hM : 0≤M) (hB : 0≤B) (hV : 0≤V)
    (hj : ∀ i : Fin (k+1), |rfcFNormalizedValueDiagonal T f G r (ε • u) k ε i-
      ε/2*inner ℝ (D (referenceStep (cgOperator base) (cgOperator base u) i.val)
        (referenceStep (cgOperator base) (cgOperator base u) i.val))
        (referenceStep (cgOperator base) (cgOperator base u) i.val)|≤J)
    (hc : |α⁻¹^2|≤M)
    (hb : ∀ i : Fin (k+1), |inner ℝ (D (referenceStep (cgOperator base) (cgOperator base u) i.val)
      (referenceStep (cgOperator base) (cgOperator base u) i.val))
      (referenceStep (cgOperator base) (cgOperator base u) i.val)|≤B)
    (hv : |α⁻¹^2-(CG.length (cgOperator base) (cgOperator base u) k)⁻¹^2|≤V) :
    ‖rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _ : Fin k => (1 : ℝ)))-
      ε • rfcFReferenceRawValueChange base D u‖≤max M 1*J+ε*(B/2)*V := by
  let x := fun i : Fin (k+1)=>rfcFNormalizedValueDiagonal T f G r (ε • u) k ε i.rev
  let y := fun i : Fin (k+1)=>(1/2 : ℝ)*inner ℝ
    (D (referenceStep (cgOperator base) (cgOperator base u) i.rev.val)
      (referenceStep (cgOperator base) (cgOperator base u) i.rev.val))
    (referenceStep (cgOperator base) (cgOperator base u) i.rev.val)
  let a := fun i : Fin (k+1)=>((Fin.cons α (fun _ : Fin k => (1 : ℝ)) : Fin (k+1) → ℝ) i)⁻¹^2
  let b := fun i : Fin (k+1)=>((Fin.cons (CG.length (cgOperator base) (cgOperator base u) k) (fun _ : Fin k => (1 : ℝ)) : Fin (k+1) → ℝ) i)⁻¹^2
  have hx i : |x i-ε*y i|≤J := by simpa only [x,y,div_eq_mul_inv,mul_assoc,one_mul] using hj i.rev
  have ha i : |a i|≤max M 1 := by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hc.trans (le_max_left _ _)
    · simp only [a,Fin.cons_succ,inv_one,one_pow,abs_one]
      exact le_max_right _ _
  have hy i : |y i|≤B/2 := by
    dsimp only [y]
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    exact (mul_le_mul_of_nonneg_left (hb i.rev) (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)
  have hab i : |a i-b i|≤V := by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hv
    · simpa only [a,b,Fin.cons_succ,inv_one,one_pow,sub_self,abs_zero] using hV
  have hh := diagonal_scalar_product_jet x y a b ε J (max M 1) (B/2) V
    hε hJ (le_trans hM (le_max_left _ _)) (by positivity) hV hx ha hy hab
  simpa only [rfcFNormalizedRawValueChange,rfcFReferenceRawValueChange,x,y,a,b,div_eq_mul_inv,inv_pow] using hh

/-- The actual raw newest-first RFC-F observed model has its genuine compact-uniform third-derivative first jet.
Article: main_krylov, prop:Fcycle(i), including the actual current-line square. -/
theorem nativeRFCF_raw_value_jet
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D₃ : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD₃ : HasFDerivAt H D₃ 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let α := rfcFActualLineScale T f G H r (ε • u) k
      ‖rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _ : Fin k => (1 : ℝ)))-
        ε • rfcFReferenceRawValueChange base D₃ u‖≤η*ε := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hpref : ∀ g∈K,∀ i<k+1,CG.gradient (cgOperator base) g i≠0 :=
    fun g hg i hi=>hpre g hg i (by omega)
  obtain ⟨ea,Ca,Ma,hea,hCa,hMa,ha⟩ := nativeRFCF_line_inverse_square base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨B,hB,hcoeff⟩ := compact_reference_cubic_bound (cgOperator base) hQ hpos D₃ k K hK hpref
  intro η hη
  let ζ := η/(2*(max Ma 1+1))
  have hζ : 0<ζ := by dsimp only [ζ]; positivity
  obtain ⟨ej,hej,hjet⟩ := nativeRFCF_value_diagonal_jet T hT f G H (cgOperator base) D₃ hD₃
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos k K hK hpref R hR ζ hζ
  let ε₀ := min ea (min ej (η/(2*((B/2)*Ca+1))))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε he u hu hKu
  have hi := ha ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hj := hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  have hh := rfcF_raw_value_jet_bound base T f G D₃ r ε _ (ζ*ε) Ma B (Ca*ε) u
    hε.le (by positivity) hMa.le hB.le (by positivity) hj hi.2.1 (hcoeff _ hKu) hi.2.2
  apply hh.trans
  have hfirst : max Ma 1*ζ≤η/2 := by
    have heq : 2*(max Ma 1+1)*ζ=η := by dsimp only [ζ]; field_simp
    nlinarith only [heq,hζ]
  have hsecond : (B/2)*Ca*ε≤η/2 := by
    have heq := (lt_div_iff₀ (by positivity : 0<2*((B/2)*Ca+1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [heq,hε]
  have hh₁ := mul_le_mul_of_nonneg_right hfirst hε.le
  have hh₂ := mul_le_mul_of_nonneg_right hsecond hε.le
  nlinarith only [hh₁,hh₂]

/-- Lipschitz original third derivatives give a genuine quadratic raw-coordinate model remainder, including the real inverse-line-square drift.
Article: main_krylov, prop:Fcycle(i), full fourth-order transfer input. -/
theorem nativeRFCF_raw_value_quartic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D₃ : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L L₃ : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD₃ : ∀ z, ‖T z‖≤r → HasFDerivAt H (D₃ z) z)
    (hDlip : LipschitzOnWith L₃ D₃ (T ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin (k+1))) r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ Cj : ℝ, 0<ε₀ ∧ 0<Cj ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let α := rfcFActualLineScale T f G H r (ε • u) k
      ‖rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _ : Fin k => (1 : ℝ)))-
        ε • rfcFReferenceRawValueChange base (D₃ 0) u‖≤Cj*ε^2 := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hpref : ∀ g∈K,∀ i<k+1,CG.gradient (cgOperator base) g i≠0 :=
    fun g hg i hi=>hpre g hg i (by omega)
  obtain ⟨ea,Ca,Ma,hea,hCa,hMa,ha⟩ := nativeRFCF_line_inverse_square base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨B,hB,hcoeff⟩ := compact_reference_cubic_bound (cgOperator base) hQ hpos (D₃ 0) k K hK hpref
  obtain ⟨ej,Cd,hej,hCd,hjet⟩ := nativeRFCF_value_diagonal_quartic T hT f G H (cgOperator base) D₃
    hr hG₀ hH₀ hHc₀ hLr hH hD₃ hDlip hF hG hQ hpos k K hK hpref R hR
  refine ⟨min ea ej,max Ma 1*Cd+(B/2)*Ca,lt_min hea hej,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hi := ha ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hj := hjet ε hε (he.trans_le (min_le_right _ _)) u hu hKu
  have hh := rfcF_raw_value_jet_bound base T f G (D₃ 0) r ε _ (Cd*ε^2) Ma B (Ca*ε) u
    hε.le (by positivity) hMa.le hB.le (by positivity) hj hi.2.1 (hcoeff _ hKu) hi.2.2
  exact hh.trans_eq (by ring)

end
end krylov.Functions
