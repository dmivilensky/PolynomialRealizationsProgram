import krylov.Convergence.ObservableRFCAccepted
import krylov.Convergence.ObservableRFCFailed
import krylov.Convergence.ObservableCycleInvariant

/-!
Article: main_krylov, apG:Dunif, complete literal observable RFC cycle.
Use: close every actual first-stopping branch and the full-memory horizon
from the true scalar source. Source: the proved actual accepted invariant,
sharp failed-energy output, derived direction domains and full projection.
No (N), reference nondegeneracy or minimum line length is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference
  krylov.Correction krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every branch of the literal observed RFC cycle has the uniform
cubic error allowance in the actual reference metric. All running
invariants are derived along execution from the primitive scalar source.
Article: main_krylov, apG:Dunif, complete local RFC theorem. -/
theorem observable_rfc_actual_cycle_bound
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (r : ℝ) (L : ℝ≥0) (S : ObservableLocalSource (metricCoordinates base hb) f G H r L)
    (m ratio : ℝ) (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (bar : ℝ) (hbar0 : 0<bar) (hbar : (n:ℝ)*bar≤1/16)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hstart : ‖metricCoordinates base hb x₀‖<r/4)
    (hsmall : (n:ℝ)*(3*(L:ℝ)*‖metricCoordinates base hb x₀‖)≤1/128)
    (hsharp : Real.sqrt n*(12*(L:ℝ)*‖metricCoordinates base hb x₀‖)≤Real.sqrt 3/(8*ratio^2))
    (hshort : 12*Real.sqrt n*(3*(L:ℝ)*‖metricCoordinates base hb x₀‖)≤bar/4) :
    ‖metricCoordinates base hb (observableRestartPoint true bar (metricCoordinates base hb) f G r n x₀)‖≤
      (256*ratio^2/bar)*observableRFCResidualBudget n
        (3*(L:ℝ)*‖metricCoordinates base hb x₀‖) ‖metricCoordinates base hb x₀‖ := by
  let T := metricCoordinates base hb
  let e := ‖T x₀‖
  let epsilon := 3*(L:ℝ)*e
  let budget := observableRFCResidualBudget n epsilon e
  let K := 256*ratio^2/bar
  let Inv := ObservableRFCInvariant T f G x₀ n epsilon bar
  let Done := fun B : History (EuclideanSpace ℝ (Fin n))=>‖T (x₀+B.displacement)‖≤K*budget
  have he : 0≤epsilon := by dsimp only [epsilon,e];positivity
  have hbudget : 0≤budget := by dsimp only [budget,observableRFCResidualBudget,e];positivity
  have hK : 0≤K := by dsimp only [K];positivity
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hbp : bar≤1/16 := by nlinarith only [mul_le_mul_of_nonneg_right hn' hbar0.le,hbar]
  have hK32 : 32*ratio≤K := by
    apply (le_div_iff₀ hbar0).mpr
    have hh := mul_le_mul_of_nonneg_left hbp (show 0≤32*ratio by linarith)
    nlinarith only [hh,hr,sq_nonneg (ratio-1)]
  have hK8 : 8≤K := (by linarith : (8:ℝ)≤32*ratio).trans hK32
  have herror (B : History (EuclideanSpace ℝ (Fin n))) (I : Inv B) :
      ‖T (x₀+B.displacement)‖≤2*‖T.symm B.gradient‖ := by
    have hh := S.gradient_error (T (x₀+B.displacement))
      (I.point.trans (by linarith only [hstart,S.radius_pos]))
    change ‖T (x₀+B.displacement)‖≤2*‖coordinateGradient T G (T (x₀+B.displacement))‖ at hh
    simpa only [coordinateGradient,T.symm_apply_apply,←I.gradient] using hh
  have hstep (B : History (EuclideanSpace ℝ (Fin n))) (hsize : B.records.length<n) (I : Inv B) :
      let A := observableRestartAdvance true bar T f G r x₀ B
      if A.reason.isSome then Done A.history else Inv A.history := by
    have hdomains := I.domains S.inverse_symmetric hn hsize.le he hbar0.le hsmall hbar
    have hunit := hdomains.1
    by_cases hz : B.gradient=0
    · have hactual : observableRestartAdvance true bar T f G r x₀ B=⟨B,some .stationary⟩ := by
        dsimp only [observableRestartAdvance]
        rw [ite_eq_left hz]
      rw [hactual]
      change ‖T (x₀+B.displacement)‖≤K*budget
      have hh := herror B I
      rw [hz,map_zero,norm_zero,mul_zero] at hh
      exact hh.trans (mul_nonneg hK hbudget)
    · by_cases hdesc : inner ℝ B.gradient (rfcFunctionDirection fullMemory B)<0
      · have hgood : ¬(¬IsUnit (crossGram (windowImages (selectedWindow fullMemory B))
            (windowSteps (selectedWindow fullMemory B))).det ∨
            ¬inner ℝ B.gradient (rfcFunctionDirection fullMemory B)<0) := by tauto
        have P := S.prepare_rfc x₀ B n epsilon bar I hn hsize he hbar0.le hsmall hbar hstart
          (by dsimp only [epsilon,e];nlinarith only [mul_nonneg L.coe_nonneg (norm_nonneg (T x₀))]) hdesc
        by_cases hfailed : bar<observableCorrectionRatio T f G r x₀ B
        · have hactual : observableRestartAdvance true bar T f G r x₀ B=
              ⟨⟨B.initial,observableRecord T f G r x₀ B 0 false::B.records⟩,some .energy⟩ := by
            dsimp only [observableRestartAdvance]
            rw [ite_eq_right hz,ite_eq_right hgood,ite_eq_left (show true=true ∧
              bar<observableCorrectionRatio T f G r x₀ B from ⟨rfl,hfailed⟩)]
          rw [hactual]
          change ‖T (x₀+(History.mk B.initial (observableRecord T f G r x₀ B 0 false::B.records)).displacement)‖≤K*budget
          have hendpoint := observableRecord_endpoint T f G r x₀ B 0 false
          simp only [add_zero] at hendpoint
          have heq : x₀+(History.mk B.initial (observableRecord T f G r x₀ B 0 false::B.records)).displacement=
              rfcFunctionLinePoint T f fullMemory r x₀ B := by
            change x₀+((observableRecord T f G r x₀ B 0 false).step+B.displacement)=_
            rw [←hendpoint]
            abel
          rw [heq]
          have hh := ObservableLocalSource.rfc_failed_error base hb f G H r L S x₀ B epsilon bar m ratio
            I P hn hsize he hbar0 hsmall hbar hm hr hlower hupper
            (by convert hsharp using 1; dsimp only [epsilon,e]; ring)
            hstart hshort hfailed
          have hcoef : 224*ratio^2/bar≤K := by dsimp only [K];gcongr; norm_num
          exact hh.trans ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left I.residual hK))
        · have hpassed : observableCorrectionRatio T f G r x₀ B≤bar := le_of_not_gt hfailed
          by_cases hgate : rfcFunctionGate fullMemory B
          · have haccept := S.rfc_accepted x₀ B n epsilon bar true I P hn hsize he hbar0.le hsmall hbar
              hstart le_rfl hpassed
            have hactual : observableRestartAdvance true bar T f G r x₀ B=
                ⟨⟨B.initial,observableRecord T f G r x₀ B
                  (rfcFunctionCorrectionStep T f G fullMemory r x₀ B) true::B.records⟩,none⟩ := by
              dsimp only [observableRestartAdvance]
              rw [ite_eq_right hz,ite_eq_right hgood,ite_eq_right (by simpa using hfailed),
                ite_eq_left (show true=true ∧ rfcFunctionGate fullMemory B ∧
                  f (rfcFunctionLinePoint T f fullMemory r x₀ B+
                    rfcFunctionCorrectionStep T f G fullMemory r x₀ B)≤
                    f (rfcFunctionLinePoint T f fullMemory r x₀ B) from ⟨rfl,hgate,haccept.1⟩)]
            rw [hactual]
            exact haccept.2
          · have hu : rfcFunctionCorrectionStep T f G fullMemory r x₀ B=0 := by
              simp only [rfcFunctionCorrectionStep,ite_eq_right hgate]
            have haccept := S.rfc_accepted x₀ B n epsilon bar false I P hn hsize he hbar0.le hsmall hbar
              hstart le_rfl hpassed
            have hactual : observableRestartAdvance true bar T f G r x₀ B=
                ⟨⟨B.initial,observableRecord T f G r x₀ B 0 false::B.records⟩,none⟩ := by
              dsimp only [observableRestartAdvance]
              rw [ite_eq_right hz,ite_eq_right hgood,ite_eq_right (by simpa using hfailed),
                ite_eq_right (by simp only [hgate,false_and,and_false,not_false_eq_true])]
            rw [hactual]
            rw [hu] at haccept
            exact haccept.2
      · have hbad : ¬IsUnit (crossGram (windowImages (selectedWindow fullMemory B))
            (windowSteps (selectedWindow fullMemory B))).det ∨
            ¬inner ℝ B.gradient (rfcFunctionDirection fullMemory B)<0 := Or.inr hdesc
        have hactual : observableRestartAdvance true bar T f G r x₀ B=⟨B,some .direction⟩ := by
          dsimp only [observableRestartAdvance]
          rw [ite_eq_right hz,ite_eq_left hbad]
        rw [hactual]
        change ‖T (x₀+B.displacement)‖≤K*budget
        have hsharp' : Real.sqrt n*(4*epsilon)≤Real.sqrt 3/(8*ratio^2) := by
          convert hsharp using 1; dsimp only [epsilon,e]; ring
        have hh := (observable_rfc_sharp_direction base hb f G x₀ B epsilon bar m ratio I hn
          hsize.le he hbar0.le hsmall hbar hm hr hlower hupper hsharp').1 (le_of_not_gt hdesc)
        have hbound := (herror B I).trans (mul_le_mul_of_nonneg_left hh (by norm_num))
        apply hbound.trans
        convert (mul_le_mul_of_nonneg_right hK32 (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left I.residual hK) using 1
        ring
  have hfull (B : History (EuclideanSpace ℝ (Fin n))) (hsize : B.records.length=n) (I : Inv B) : Done B := by
    have hdomains := I.domains S.inverse_symmetric hn hsize.le he hbar0.le hsmall hbar
    let s := unitWindow (observablePrimal T B)
    have hform (c : Fin B.pairs.length → ℝ) : (3/4:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram s s*ᵥc) :=
      (observable_coefficient_sandwich _ hdomains.2.2.1 c).1
    have hdim : B.pairs.length=Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [History.pairs_length,hsize];simp
    have hp := observedProjection_residual_bound s (hdomains.2.2.1.trans (by norm_num)) (T.symm B.gradient)
    rw [observable_full_projection s (3/4) (by norm_num) hdim hform] at hp
    have hbound := (herror B I).trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    apply hbound.trans
    convert (mul_le_mul_of_nonneg_right hK8 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left I.residual hK) using 1
    ring
  exact observable_cycle_invariant true bar T f G r x₀ n Inv Done hstep hfull n
    ⟨G x₀,[]⟩ (by simp) (observable_rfc_initial_invariant T f G x₀ n epsilon bar)

end
end krylov.Convergence
