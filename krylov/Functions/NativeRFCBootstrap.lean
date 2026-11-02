import krylov.Functions.NativeRFCNormalized

/-!
Article: main_krylov, lem:cycle-transfer, genuine ordinary RFC finite bootstrap.
Use: derive all actual search/correction query enclosures, full native/operator
history equality, and quadratic reference step errors from primitive f/G/H.
The proof first estimates each correction against a dummy current operator;
only after its endpoint is enclosed is its genuine Hessian average queried.
Source: compact ordinary RFC stability, exact search localization and the FTC.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The proved quantitative prefix invariant of a genuine ordinary RFC run.
Article: main_krylov, lem:cycle-transfer. Each operator is its actual segment
average, every query is a true function query, and every history retains its
full actual one-query trace. -/
def NativeRFCPrefixBounds (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (k : ℕ) : Prop :=
  let x₀ := ε • u
  let A := rfcFunctionSearchOperator T f G H fullMemory r x₀
  let B := rfcFunctionCorrectionOperator T f G H fullMemory r x₀
  (∀ j≤k, ‖rfcFunctionPoint T f G fullMemory r x₀ j‖≤M*ε ∧
    rfcFunctionRun T f G fullMemory r x₀ j=methodRun (rfcMethod fullMemory 1) A B (G x₀) j) ∧
  ∀ j<k,
    ‖A j-Q‖≤D*ε ∧ ‖B j-Q‖≤D*ε ∧
    ‖rfcFunctionLinePoint T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ j)‖≤M*ε ∧
    ‖rfcFunctionCorrectionStep T f G fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ j)‖≤C*ε^2 ∧
    ‖(rfcFunctionRecord T f G fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ j)).step-
      ε • referenceStep Q (Q u) j‖≤C*ε^2

variable [FiniteDimensional ℝ E]

set_option maxHeartbeats 1600000 in
/-- Every finite true ordinary RFC cycle has a common compact-reference
neighborhood with actual O(ε) queries, actual O(ε²) correction queries and
reference step errors, and a faithful full operator transcript.
Article: main_krylov, lem:cycle-transfer, ordinary RFC.
No query bounds, segment identities, nonzero actual searches or output
remainders occur in the assumptions. -/
theorem nativeRFC_compact_prefix (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ M D C : ℝ, 0<ε₀ ∧ 0<M ∧ 0<D ∧ 0<C ∧
      ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : E, ‖u‖≤R → Q u∈K →
        NativeRFCPrefixBounds T f G H Q r u ε M D C N := by
  obtain ⟨δf,Cf,hδf,hCf,hfields⟩ := compact_rfc_reference_field_changes Q hQ hpos N K hK hpre
  obtain ⟨δd,hδd,hdomains⟩ := compact_rfc_reference_search_domain Q hQ hpos N K hK hpre
  let δ := min δf δd
  have hδ : 0<δ := lt_min hδf hδd
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Dg := P/2*R^2
  have hP : 0≤P := NNReal.coe_nonneg _
  have hDg : 0≤Dg := by dsimp only [Dg]; positivity
  have hprefix : ∀ k≤N, ∃ ε₀ M D C : ℝ, 0<ε₀ ∧ 0<M ∧ 0<D ∧ 0<C ∧
      ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : E, ‖u‖≤R → Q u∈K →
        NativeRFCPrefixBounds T f G H Q r u ε M D C k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1,R+1,1,1,by norm_num,by positivity,by norm_num,by norm_num,?_⟩
      intro ε hε _ u hu _
      constructor
      · intro j hj
        have he : j=0 := by omega
        subst j
        refine ⟨?_,rfl⟩
        simpa [rfcFunctionPoint,rfcFunctionRun,History.displacement,norm_smul,Real.norm_of_nonneg hε.le,mul_comm]
          using (mul_le_mul_of_nonneg_left (hu.trans (by linarith : R≤R+1)) hε.le)
      · intro j hj
        omega
    | succ k ih =>
      intro hkN
      have hk : k<N := by omega
      obtain ⟨ep,M,D,C,hep,hM,hD,hC,hprev⟩ := ih (by omega)
      let My := ‖T.symm.toContinuousLinearMap‖*Real.sqrt 3*‖T.toContinuousLinearMap‖*M
      let Da := P/2*(M+My)
      let Dt := Dg+D+Da+1
      let Cu := Cf*Dt
      let Mn := M+My+1
      let Db := P/2*(My+Mn)
      have hMy : 0≤My := by dsimp only [My]; positivity
      have hDa : 0≤Da := by dsimp only [Da]; positivity
      have hDt : 0<Dt := by dsimp only [Dt]; positivity
      have hCu : 0<Cu := mul_pos hCf hDt
      have hMn : 0<Mn := by dsimp only [Mn]; positivity
      have hDb : 0≤Db := by dsimp only [Db]; positivity
      let en := min ep (min (r/(4*(‖T.toContinuousLinearMap‖*M+1)))
        (min (δ/(Dt+1)) (min (1/(Cu+1)) (r/(2*(‖T.toContinuousLinearMap‖*Mn+1))))))
      have hen : 0<en := by dsimp only [en]; positivity
      refine ⟨en,Mn,D+Da+Db+1,C+Cu+1,hen,hMn,by positivity,by positivity,?_⟩
      intro ε hε he u hu hKu
      have heold : ε<ep := he.trans_le (min_le_left _ _)
      have heinput : ε<r/(4*(‖T.toContinuousLinearMap‖*M+1)) :=
        he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hetube : ε<δ/(Dt+1) :=
        he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      have hequery : ε<1/(Cu+1) :=
        he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
      have henew : ε<r/(2*(‖T.toContinuousLinearMap‖*Mn+1)) :=
        he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      have hp := hprev ε hε heold u hu hKu
      let x₀ := ε • u
      let X := rfcFunctionPoint T f G fullMemory r x₀
      let S := rfcFunctionRun T f G fullMemory r x₀
      let Y := rfcFunctionLinePoint T f fullMemory r x₀ (S k)
      let U := rfcFunctionCorrectionStep T f G fullMemory r x₀ (S k)
      let A := rfcFunctionSearchOperator T f G H fullMemory r x₀
      let B := rfcFunctionCorrectionOperator T f G H fullMemory r x₀
      have hx : ‖X k‖≤M*ε := (hp.1 k le_rfl).1
      have hhistory : S k=methodRun (rfcMethod fullMemory 1) A B (G x₀) k := (hp.1 k le_rfl).2
      have hxmetric : ‖T (X k)‖<r/2 := by
        have hb := (T.toContinuousLinearMap.le_opNorm (X k)).trans
          (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
        have he' := (lt_div_iff₀ (by positivity : 0<4*(‖T.toContinuousLinearMap‖*M+1))).mp heinput
        change ‖T (X k)‖≤‖T.toContinuousLinearMap‖*(M*ε) at hb
        nlinarith only [hb,he',hε,norm_nonneg (T (X k))]
      have hyb := metricLocalExactPoint_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG
        (X k) (rfcFunctionDirection fullMemory (S k)) hxmetric
      have hyMetric : ‖T Y‖<r := hyb.2
      have hy : ‖Y‖≤My*ε := by
        calc
          _ = ‖T.symm (T Y)‖ := by rw [T.symm_apply_apply]
          _ ≤ ‖T.symm.toContinuousLinearMap‖*‖T Y‖ := T.symm.toContinuousLinearMap.le_opNorm _
          _ ≤ ‖T.symm.toContinuousLinearMap‖*(Real.sqrt 3*‖T (X k)‖) :=
            mul_le_mul_of_nonneg_left hyb.1 (norm_nonneg _)
          _ ≤ ‖T.symm.toContinuousLinearMap‖*(Real.sqrt 3*(‖T.toContinuousLinearMap‖*(M*ε))) := by
            gcongr
            exact (T.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
          _ = My*ε := by ring
      have hAcurr : ‖A k-Q‖≤Da*ε := by
        have hb := metric_segment_operator_bound T H hr.le hH (X k) Y
          (by linarith) hyMetric.le
        rw [hH₀] at hb
        change ‖A k-Q‖≤P/2*(‖X k‖+‖Y‖) at hb
        exact hb.trans (by dsimp only [Da]; nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hx hy) (by positivity : 0≤P/2)])
      have hx₀metric : ‖T x₀‖≤r := by
        have hb := (T.toContinuousLinearMap.le_opNorm (X 0)).trans
          (mul_le_mul_of_nonneg_left (hp.1 0 (by omega)).1 (norm_nonneg _))
        have he' := (lt_div_iff₀ (by positivity : 0<4*(‖T.toContinuousLinearMap‖*M+1))).mp heinput
        have heq : X 0=x₀ := by simp [X,rfcFunctionPoint,rfcFunctionRun,History.displacement]
        rw [heq] at hb
        change ‖T x₀‖≤‖T.toContinuousLinearMap‖*(M*ε) at hb
        nlinarith only [hb,he',hε,norm_nonneg (T x₀)]
      let v := ε⁻¹ • G x₀-Q u
      have hv : ‖v‖≤Dg*ε := by
        have hb := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG x₀ hx₀metric
        have hvEq : v=ε⁻¹ • (G x₀-Q x₀) := by
          dsimp only [v,x₀]
          rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
        rw [hvEq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
        have hs : ‖u‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hu
        rw [show x₀=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le] at hb
        calc
          _ ≤ ε⁻¹*(P/2*(ε*‖u‖)^2) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hε.le)
          _ = P/2*‖u‖^2*ε := by field_simp
          _ ≤ Dg*ε := by dsimp only [Dg]; nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0≤P/2*ε)]
      let Θ : Fin N → E →L[ℝ] E := fun j=>if j.val≤k then A j.val-Q else 0
      let Ξ : Fin N → E →L[ℝ] E := fun j=>if j.val<k then B j.val-Q else 0
      let An := fcFiniteOperatorPath Q N Θ
      let Bn := fcFiniteOperatorPath Q N Ξ
      have hΘ : ‖Θ‖≤(D+Da)*ε := by
        apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(D+Da)*ε)).mpr
        intro j
        by_cases hj : j.val≤k
        · simp only [Θ,ite_eq_left hj]
          by_cases heq : j.val=k
          · rw [heq]
            exact hAcurr.trans (mul_le_mul_of_nonneg_right (by linarith only [hD] : Da≤D+Da) hε.le)
          · exact (hp.2 j.val (by omega)).1.trans (mul_le_mul_of_nonneg_right (by linarith only [hDa] : D≤D+Da) hε.le)
        · simp only [Θ,ite_eq_right hj,norm_zero]
          positivity
      have hΞ : ‖Ξ‖≤D*ε := by
        apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤D*ε)).mpr
        intro j
        by_cases hj : j.val<k
        · simpa only [Ξ,ite_eq_left hj] using (hp.2 j.val hj).2.1
        · simp only [Ξ,ite_eq_right hj,norm_zero]
          positivity
      have ht : ‖(v,(Θ,Ξ))‖≤Dt*ε := by
        simp only [Prod.norm_def,max_le_iff]
        exact ⟨hv.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hD,hDa]) hε.le),hΘ.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hDg]) hε.le),
          hΞ.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hDg,hDa]) hε.le)⟩
      have hsmall : ‖(v,(Θ,Ξ))‖≤δ := by
        have hb := (lt_div_iff₀ (by positivity : 0<Dt+1)).mp hetube
        exact ht.trans (by nlinarith only [hb,hε])
      have hnormf := hfields (Q u) hKu v Θ Ξ (hsmall.trans (min_le_left _ _)) k hk
      have hdom := hdomains (Q u) hKu v Θ Ξ (hsmall.trans (min_le_right _ _)) k hk
      have hinit : G x₀=ε • (Q u+v) := by
        dsimp only [v]
        rw [add_sub_cancel,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
      have hAn j (hj : j≤k) : A j=An j := by
        have hjN : j<N := by omega
        simp only [An,fcFiniteOperatorPath,dite_eq_left hjN,Θ,ite_eq_left hj]
        abel
      have hBn j (hj : j<k) : B j=Bn j := by
        have hjN : j<N := by omega
        simp only [Bn,fcFiniteOperatorPath,dite_eq_left hjN,Ξ,ite_eq_left hj]
        abel
      have hhn : S k=methodRun (rfcMethod fullMemory 1) An Bn (ε • (Q u+v)) k := by
        rw [hhistory,hinit]
        exact methodRun_congr_prefix _ _ _ _ _ _ _ (fun j hj=>hAn j hj.le) hBn
      have hline := rfcFunctionLine_operator T hT f G H hr hG₀ hHc₀ hLr hH hF hG fullMemory x₀ (S k)
        (rfcFunctionRun_gradient T f G fullMemory r x₀ k) hxmetric
      change rfcFunctionLineStep T f fullMemory r x₀ (S k)=
        lineLength (S k).gradient (rfcFunctionDirection fullMemory (S k)) (A k (rfcFunctionDirection fullMemory (S k))) • _ ∧
        G Y=searchedGradient (S k).gradient (rfcFunctionDirection fullMemory (S k)) (A k (rfcFunctionDirection fullMemory (S k))) at hline
      rw [hAn k le_rfl] at hline
      have hqueryBound := rfcFunctionCorrectionStep_finite_bound T f G r x₀ (S k) An Bn
        (Q u+v) ε Cf ‖(v,(Θ,Ξ))‖ hε k hhn hline.1 hline.2 hdom hnormf.2.2
      have hU : ‖U‖≤Cu*ε^2 := hqueryBound.2.2.trans (by
        have hb := mul_le_mul_of_nonneg_left ht (by positivity : 0≤ε*Cf)
        dsimp only [Cu]
        nlinarith only [hb])
      have hUlinear : ‖U‖≤ε := by
        have hb := (lt_div_iff₀ (by positivity : 0<Cu+1)).mp hequery
        exact hU.trans (by nlinarith only [hb,hε])
      have hpoint : X (k+1)=Y+U := rfcFunctionPoint_succ_line T f G fullMemory r x₀ k
      have hxnew : ‖X (k+1)‖≤Mn*ε := by
        rw [hpoint]
        exact (norm_add_le _ _).trans ((add_le_add hy hUlinear).trans (by dsimp only [Mn]; nlinarith only [hM,hMy,hε]))
      have hxnewMetric : ‖T (X (k+1))‖<r := by
        have hb := (T.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxnew (norm_nonneg _))
        have he' := (lt_div_iff₀ (by positivity : 0<2*(‖T.toContinuousLinearMap‖*Mn+1))).mp henew
        change ‖T (X (k+1))‖≤‖T.toContinuousLinearMap‖*(Mn*ε) at hb
        nlinarith only [hb,he',hε,norm_nonneg (T (X (k+1)))]
      have hBcurr : ‖B k-Q‖≤Db*ε := by
        have hb := metric_segment_operator_bound T H hr.le hH Y (X (k+1)) hyMetric.le hxnewMetric.le
        rw [hH₀,hpoint,add_sub_cancel_left] at hb
        have hBk : B k=averagedDerivative H Y U := rfl
        rw [←hBk,←hpoint] at hb
        change ‖B k-Q‖≤P/2*(‖Y‖+‖X (k+1)‖) at hb
        exact hb.trans (by dsimp only [Db]; nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hy hxnew) (by positivity : 0≤P/2)])
      have hquery : G (Y+U)=G Y+B k U := by
        have hb := metric_segment_gradient T G H hH hG Y (Y+U) hyMetric.le (by rw [←hpoint]; exact hxnewMetric.le)
        have hBk : B k=averagedDerivative H Y U := rfl
        rw [add_sub_cancel_left,←hBk] at hb
        exact hb
      have hα : lineLength (S k).gradient (rfcFunctionDirection fullMemory (S k))
          (A k (rfcFunctionDirection fullMemory (S k)))≠0 := by
        rw [hAn k le_rfl]
        exact hqueryBound.2.1
      have hrecord := rfcFunctionRecord_operator T f G fullMemory r x₀ (S k) (A k) (B k)
        hqueryBound.1 hα (by rw [hAn k le_rfl]; exact hline.1)
        (by rw [hAn k le_rfl]; exact hline.2) hquery
      have hhistoryNew : S (k+1)=methodRun (rfcMethod fullMemory 1) A B (G x₀) (k+1) := by
        change (⟨(S k).initial,rfcFunctionRecord T f G fullMemory r x₀ (S k)::(S k).records⟩ : History E)=_
        rw [←hrecord,hhistory]
        rfl
      have hsec : G Y-(S k).gradient=
          lineLength (S k).gradient (rfcFunctionDirection fullMemory (S k)) (An k (rfcFunctionDirection fullMemory (S k))) •
            An k (rfcFunctionDirection fullMemory (S k)) := by
        rw [hline.2,searchedGradient]
        abel
      have huPhase := rfcFunctionCorrectionStep_operator T f G fullMemory r x₀ (S k) (An k) (Bn k)
        _ hqueryBound.2.1 hline.1 hsec hline.2
      have hstepFinite : (rfcFunctionRecord T f G fullMemory r x₀ (S k)).step=
          probedStep (rfcMethod fullMemory 1) An Bn (ε • (Q u+v)) k := by
        change rfcFunctionLineStep T f fullMemory r x₀ (S k)+U=_
        rw [hline.1]
        change _+rfcFunctionCorrectionStep T f G fullMemory r x₀ (S k)=_
        rw [huPhase,hhn]
        rfl
      have hstepError : ‖(rfcFunctionRecord T f G fullMemory r x₀ (S k)).step-
          ε • referenceStep Q (Q u) k‖≤Cu*ε^2 := by
        rw [hstepFinite,(rfc_scalar fullMemory 1 An Bn (Q u+v) ε hε.ne' N).2 k hk |>.2.1,
          ←smul_sub,norm_smul,Real.norm_of_nonneg hε.le]
        have hb := mul_le_mul_of_nonneg_left hnormf.2.1 hε.le
        have hb' := mul_le_mul_of_nonneg_left ht (by positivity : 0≤ε*Cf)
        dsimp only [Cu]
        nlinarith only [hb,hb']
      have hMM : M≤Mn := by dsimp only [Mn]; linarith only [hMy]
      have hMyM : My≤Mn := by dsimp only [Mn]; linarith only [hM]
      have hDD : D≤D+Da+Db+1 := by linarith only [hDa,hDb]
      have hDaD : Da≤D+Da+Db+1 := by linarith only [hD,hDb]
      have hDbD : Db≤D+Da+Db+1 := by linarith only [hD,hDa]
      have hCC : C≤C+Cu+1 := by linarith only [hCu]
      have hCuC : Cu≤C+Cu+1 := by linarith only [hC]
      constructor
      · intro j hj
        by_cases heq : j=k+1
        · subst j
          exact ⟨hxnew,hhistoryNew⟩
        · have hj' : j≤k := by omega
          exact ⟨(hp.1 j hj').1.trans (mul_le_mul_of_nonneg_right hMM hε.le), (hp.1 j hj').2⟩
      · intro j hj
        by_cases heq : j=k
        · subst j
          exact ⟨hAcurr.trans (mul_le_mul_of_nonneg_right hDaD hε.le),hBcurr.trans (mul_le_mul_of_nonneg_right hDbD hε.le),
            hy.trans (mul_le_mul_of_nonneg_right hMyM hε.le),hU.trans (mul_le_mul_of_nonneg_right hCuC (sq_nonneg ε)),
            hstepError.trans (mul_le_mul_of_nonneg_right hCuC (sq_nonneg ε))⟩
        · obtain ⟨ha,hb,hy',hu',hs⟩ := hp.2 j (by omega)
          exact ⟨ha.trans (mul_le_mul_of_nonneg_right hDD hε.le),hb.trans (mul_le_mul_of_nonneg_right hDD hε.le),
            hy'.trans (mul_le_mul_of_nonneg_right hMM hε.le),hu'.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg ε)),
            hs.trans (mul_le_mul_of_nonneg_right hCC (sq_nonneg ε))⟩
  exact hprefix N le_rfl

end
end krylov.Functions
