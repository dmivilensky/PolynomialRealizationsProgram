import krylov.Functions.NativeRFCJetCoordinates

/-!
Article: main_krylov, thm:Htransfer, true ordinary RFC tensor substitution.
Use: compare the physical quadratic response of all genuine objective queries
with its actual third-derivative response at the quadratic reference nodes.
Source: the proved native bootstrap, genuine Schwarz symmetry and compact
bounded bilinearity of the actual RFC quadratic coefficient.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- True third-derivative search slices, including the common first secant.
Article: main_krylov, thm:Htransfer. -/
def rfcTensorSearch {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E) (u : E) (i : ℕ) : E →L[ℝ] E :=
  Q+D (rfcReferenceSearchMidpoint Q u i)

/-- True third-derivative correction slices at the next quadratic nodes.
Article: main_krylov, thm:Htransfer. -/
def rfcTensorCorrection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E) (u : E) (i : ℕ) : E →L[ℝ] E :=
  Q+D (fcQuadraticReferencePoint Q u (i+1))

/-- The actual physical cubic RFC coefficient, formed from the original third
Hessian derivative and true quadratic reference positions.
Article: main_krylov, thm:Htransfer. -/
def rfcTensorPhysicalCoefficient (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  rfcPhysicalQuadratic base (cgOperator base u)
    (rfcTensorSearch (cgOperator base) D u) (rfcTensorCorrection (cgOperator base) D u)

set_option maxHeartbeats 800000 in
/-- Uniform substitution of any genuine operator-jet error into the true
physical RFC quadratic response gains one further factor of the initial
scale. Every symmetry, source bound and coefficient bound is derived from
the original objective, uniformly on a compact nondegenerate reference family.
Article: main_krylov, thm:Htransfer. -/
theorem nativeRFC_tensor_comparison
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0≤C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      ∀ J : ℝ, 0≤J →
      (∀ j<k+1,
        ‖rfcFunctionSearchOperator T f G H fullMemory r (ε • u) j-cgOperator base-
          ε • D (rfcReferenceSearchMidpoint (cgOperator base) u j)‖≤J ∧
        ‖rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) j-cgOperator base-
          ε • D (fcQuadraticReferencePoint (cgOperator base) u (j+1))‖≤J) →
      ‖rfcPhysicalQuadratic base (cgOperator base u)
          (rfcFunctionSearchOperator T f G H fullMemory r (ε • u))
          (rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u))-
        ε^2 • rfcTensorPhysicalCoefficient base D u‖≤C*ε*J := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hpref : ∀ g∈K, ∀ i<k+1, CG.gradient Q g i≠0 := fun g hg i hi=>hpre g hg i (by omega)
  obtain ⟨ep,M,Ds,Cp,hep,hM,hDs,_,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK hpref R hR
  obtain ⟨ej,hej,hjets⟩ := nativeRFC_reference_operator_jets T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK hpref R hR 1 zero_lt_one
  obtain ⟨Mb,hMb,hresponse⟩ := compact_rfcPhysicalQuadratic_difference base hb K hK hpre
  let e := min ep ej/2
  have he : 0<e := by dsimp only [e]; positivity
  have heep : e<ep := by have hh := min_le_left ep ej; dsimp only [e]; linarith only [hh,hep]
  have heej : e<ej := by have hh := min_le_right ep ej; dsimp only [e]; linarith only [hh,hej]
  have hleading (u : EuclideanSpace ℝ (Fin (k+1))) (hu : ‖u‖≤R) (hKu : Q u∈K) (j : ℕ) (hj : j<k+1) :
      ‖D (rfcReferenceSearchMidpoint Q u j)‖≤Ds+1 ∧
      ‖D (fcQuadraticReferencePoint Q u (j+1))‖≤Ds+1 := by
    have hp := hprefix e he heep u hu hKu
    have hz := hjets e he heej u hu hKu j hj
    simp only [one_mul] at hz
    exact ⟨leading_norm_bound_of_jet _ _ e Ds he (hp.2 j hj).1 hz.1,
      leading_norm_bound_of_jet _ _ e Ds he (hp.2 j hj).2.1 hz.2⟩
  let ε₀ := min ep (r/(‖T.toContinuousLinearMap‖*M+1))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Mb*(Ds+(Ds+1)),hε₀,by positivity,?_⟩
  intro ε hε hεsmall u hu hKu J hJ hjets'
  have hp := hprefix ε hε (hεsmall.trans_le (min_le_left _ _)) u hu hKu
  have hscale : ‖T.toContinuousLinearMap‖*(M*ε)<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*M+1)).mp
      (hεsmall.trans_le (min_le_right _ _))
    nlinarith only [hh,hε]
  have hsym := hp.operator_symmetric T f G H Q r u ε M Ds Cp (k+1) hscale hH hF hG
  have hs (v : EuclideanSpace ℝ (Fin (k+1))) := genuine_third_slice_symmetric T f G H D hD hr hF hG v
  have hAs j (_hj : j<k+1) : (rfcTensorSearch Q D u j).toLinearMap.IsSymmetric := hQ.add (hs _)
  have hBs j (_hj : j<k+1) : (rfcTensorCorrection Q D u j).toLinearMap.IsSymmetric := hQ.add (hs _)
  have hAn j (hj : j<k+1) : ‖rfcTensorSearch Q D u j-Q‖≤Ds+1 := by
    simpa only [rfcTensorSearch,add_sub_cancel_left] using (hleading u hu hKu j hj).1
  have hBn j (hj : j<k+1) : ‖rfcTensorCorrection Q D u j-Q‖≤Ds+1 := by
    simpa only [rfcTensorCorrection,add_sub_cancel_left] using (hleading u hu hKu j hj).2
  exact rfcPhysicalQuadratic_jet_bound base hQ (Q u) _ _
    (rfcTensorSearch Q D u) (rfcTensorCorrection Q D u)
    (fun j hj=>(hsym j hj).1) (fun j hj=>(hsym j hj).2) hAs hBs
    ε Ds (Ds+1) J Mb hε hDs.le (by positivity) hJ hMb
    (fun j hj=>(hp.2 j hj).1) (fun j hj=>(hp.2 j hj).2.1) hAn hBn
    (fun j hj=>by simpa only [rfcTensorSearch,Q,add_sub_cancel_left] using (hjets' j hj).1)
    (fun j hj=>by simpa only [rfcTensorCorrection,Q,add_sub_cancel_left] using (hjets' j hj).2)
    (hresponse (Q u) hKu)

end
end krylov.Functions
