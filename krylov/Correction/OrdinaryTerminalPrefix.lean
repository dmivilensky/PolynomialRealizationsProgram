import krylov.Correction.RFCUniformNonstagnation
import krylov.Correction.RFCUniformContamination
import krylov.Correction.UniformModelBounds
import krylov.Correction.RecordedPrefixReindex

/-!
Article: main_krylov, thm:UCq, unified genuine ordinary terminal prefix.
Use: Choose one common tube before the reference and source data, retaining
actual old angles, projected gradients, step stability and measured contamination.
Source: the proved true nonstagnating prefix and contamination inductions,
real accepted-history equality and genuine chronological observed indexing.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- True quadratic measured-secant contamination and an actual near-identity operator imply the genuine linear relative pair allowance.
Use: Obtain observed search conditioning directly from the proved measured contamination.
Article: main_krylov, thm:UCq.
Proof: Split the true pair difference through its own operator image and bound that image by the actual operator norm; the unit radius absorbs one factor of the quadratic budget.
-/
theorem observed_pair_error_of_quadratic_contamination {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E →L[ℝ] E) (s y : E)
    {C ε : ℝ} (hC : 0≤C) (hε : 0≤ε) (hε1 : ε≤1)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ‖y-A s‖≤C*ε^2*‖s‖) : ‖y-s‖≤(1+C)*ε*‖s‖ := by
  have hAs : ‖A s-s‖≤ε*‖s‖ := by
    exact ((A-ContinuousLinearMap.id ℝ E).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hsq : ε^2≤ε := by nlinarith
  calc
    _ ≤ ‖y-A s‖+‖A s-s‖ := norm_sub_le_norm_sub_add_norm_sub y (A s) s
    _ ≤ C*ε^2*‖s‖+ε*‖s‖ := add_le_add hy hAs
    _ ≤ C*ε*‖s‖+ε*‖s‖ := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- One genuine ordinary-RFC tube simultaneously supplies every actual active observed model, complete shadow-prefix equality and the true chronological terminal recorded-step, residual and quadratic contamination bounds.
Use: Assemble the whole spectral-class ordinary terminal response with constants chosen before every actual reference and source run.
Article: main_krylov, thm:UCq.
Proof: Add the three proved nonstagnation constants and intersect their genuine positive radii. Exact complete accepted-history equality transfers real gradients, recorded steps and measured secants to ordinary RFC. The true chronological reindexing preserves the actual old projected residual and angle bounds. Every quantitative premise comes from a proved actual finite-prefix induction.
-/
theorem ordinary_uniform_terminal_prefix (n : ℕ) (hn : 2≤n) (κ : ℝ) (hκ : 1≤κ) :
    ∃ M₀ δ a C D Cξ Cₘ : ℝ,
      0<M₀ ∧ 0<δ ∧ 0<a ∧ 0<C ∧ 0<D ∧ 0<Cξ ∧ 0<Cₘ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤δ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
      let R := cgOperator (metricRoot base)
      let J := cgOperator (metricRoot base)⁻¹
      activeObservedModelBounds base m A B g n (1/2) Cₘ ε ∧
      (∀ j≤n-1, methodRun (gatedMethod fullMemory (1/2)) A B g j=methodRun m A B g j) ∧
      recordedPrefixBound (a*ε) C ε
        (fun i : Fin (n-1) => R (probedStep m A B g i.val))
        (J (probedGradient m A B g (n-1))) ∧
      ∀ i<n-1, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤D*ε ∧
        ‖J (probedSecant m A B g i)-canonicalOperator base (A i) (R (probedStep m A B g i))‖≤
          Cξ*ε^2*‖R (probedStep m A B g i)‖ := by
  obtain ⟨Mp,δp,a,C,D,hMp,hδp,ha,hC,hD,hprefix⟩ :=
    gated_uniform_nonstagnating_prefix n hn κ (1/2) hκ (by norm_num) (by norm_num)
  obtain ⟨Mm,δm,Cm,hMm,hδm,hCm,hmodels⟩ := ordinary_uniform_nonstagnating_models n hn κ hκ
  obtain ⟨Mx,δx,Cx,hMx,hδx,hCx,hcontam⟩ :=
    gated_uniform_nonstagnating_contamination n hn κ (1/2) hκ (by norm_num) (by norm_num)
  refine ⟨Mp+Mm+Mx,min δp (min δm δx),a,C,D,Cx,Cm,
    by positivity,lt_min hδp (lt_min hδm hδx),ha,hC,hD,hCx,hCm,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  have hNp : Mp*ε≤‖cgCanonicalError base g (n-2)‖ :=
    (mul_le_mul_of_nonneg_right (by linarith : Mp≤Mp+Mm+Mx) hε.le).trans hN
  have hNm : Mm*ε≤‖cgCanonicalError base g (n-2)‖ :=
    (mul_le_mul_of_nonneg_right (by linarith : Mm≤Mp+Mm+Mx) hε.le).trans hN
  have hNx : Mx*ε≤‖cgCanonicalError base g (n-2)‖ :=
    (mul_le_mul_of_nonneg_right (by linarith : Mx≤Mp+Mm+Mx) hε.le).trans hN
  have hep := he.trans (min_le_left _ _)
  have hem := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hex := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp := hprefix base hb μ hμ hspec A B g ε hε hep hinit hpre hNp hA hB (n-1) le_rfl
  have hm := hmodels base hb μ hμ hspec A B g ε hε hem hinit hpre hNm hA hB
  have hx := hcontam base hb μ hμ hspec A B g ε hε hex hinit hpre hNx hA hB
  dsimp only at hp hm hx ⊢
  let mg := gatedMethod fullMemory (1/2) (E := EuclideanSpace ℝ (Fin n))
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  have heq := hm.1
  have hgrad j (hj : j≤n-1) : probedGradient mg A B g j=probedGradient m A B g j :=
    congrArg History.gradient (heq j hj)
  have hstep j (hj : j<n-1) : probedStep mg A B g j=probedStep m A B g j :=
    congrArg (fun H : History (EuclideanSpace ℝ (Fin n)) => H.observationList.getD 4 0)
      (heq (j+1) (by omega))
  have hsecant j (hj : j<n-1) : probedSecant mg A B g j=probedSecant m A B g j := by
    rw [probedSecant,probedSecant,hgrad (j+1) (by omega),hgrad j hj.le]
  refine ⟨?_,heq,?_,?_⟩
  · dsimp only [activeObservedModelBounds]
    intro j hj hd
    have ht := hm.2 j hj hd
    refine ⟨ht.1,ht.2.1,ht.2.2.1,?_⟩
    rw [canonicalObservedModel_augmented base hb]
    exact ht.2.2.2
  · have hrp := hp.2.1
    change recordedPrefixBound (a*ε) C ε
      (primalWindow base (windowSteps (selectedWindow fullMemory (methodRun mg A B g (n-1)))))
      (cgOperator (metricRoot base)⁻¹ (probedGradient mg A B g (n-1))) at hrp
    rw [heq (n-1) le_rfl,hgrad (n-1) le_rfl,fullWindow_methodRun] at hrp
    exact (recordedPrefixBound_executed_chronological (probedStep m A B g) (probedSecant m A B g)
      (cgOperator (metricRoot base)) (cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (n-1)))
      (n-1) (a*ε) C ε).mp hrp
  · intro i hi
    have hs := hp.2.2 i hi
    have hxi := hx i hi
    rw [hstep i hi] at hs hxi
    rw [hsecant i hi] at hxi
    exact ⟨hs,hxi⟩

end
end krylov.Correction
