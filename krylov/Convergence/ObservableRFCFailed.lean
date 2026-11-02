import krylov.Convergence.ObservableRFCSharp
import krylov.Convergence.ObservableGradientError

/-!
Article: main_krylov, apG:Dunif, the actual failed-energy output.
Use: control the already evaluated line endpoint returned by the real
early restart. Source: the actual short-line estimate, sharp physical
direction geometry and the true local gradient/error comparison.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- A failed actual RFC energy gate returns a genuinely cubically small
line endpoint. The bound depends on the real old projected residual,
with no hypothesis on the minimum length of any executed line.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.rfc_failed_error
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (r : ℝ) (L : ℝ≥0) (S : ObservableLocalSource (metricCoordinates base hb) f G H r L)
    (x₀ : EuclideanSpace ℝ (Fin n)) (B : History (EuclideanSpace ℝ (Fin n)))
    (epsilon bar m ratio : ℝ)
    (I : ObservableRFCInvariant (metricCoordinates base hb) f G x₀ n epsilon bar B)
    (P : ObservableRFCPrepared (metricCoordinates base hb) f G H r x₀ B epsilon)
    (hn : 1≤n) (hsize : B.records.length<n) (he : 0≤epsilon) (hbar0 : 0<bar)
    (hsmall : (n:ℝ)*epsilon≤1/128) (hbar : (n:ℝ)*bar≤1/16)
    (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (hsharp : Real.sqrt n*(4*epsilon)≤Real.sqrt 3/(8*ratio^2))
    (hstart : ‖metricCoordinates base hb x₀‖<r/4)
    (hshort : 12*Real.sqrt n*epsilon≤bar/4)
    (hfailed : bar<observableCorrectionRatio (metricCoordinates base hb) f G r x₀ B) :
    let T := metricCoordinates base hb
    ‖T (rfcFunctionLinePoint T f fullMemory r x₀ B)‖≤
      (224*ratio^2/bar)*‖projectedResidual (unitWindow (observablePrimal T B)) (T.symm B.gradient)‖ := by
  let T := metricCoordinates base hb
  let g := T.symm B.gradient
  let d := T (rfcFunctionDirection fullMemory B)
  let A := observableRFCSearchOperator T f H r x₀ B
  let alpha := lineLength g d (A d)
  let line := T (rfcFunctionLineStep T f fullMemory r x₀ B)
  let R := ‖projectedResidual (unitWindow (observablePrimal T B)) g‖
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hep : epsilon≤1/128 := by nlinarith only [mul_le_mul_of_nonneg_right hn' he,hsmall]
  have hbp : bar≤1/16 := by nlinarith only [mul_le_mul_of_nonneg_right hn' hbar0.le,hbar]
  have hA : ‖A‖≤(9/8:ℝ) := by
    have hh := norm_add_le (A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    rw [sub_add_cancel] at hh
    have hi := ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=EuclideanSpace ℝ (Fin n))
    linarith only [hh,hi,P.operator,hep]
  have hcurv : inner ℝ d (A d)≠0 := by
    have hh := observable_operator_form A epsilon P.operator d
    have hp := norm_pos_iff.mpr P.direction
    have hh' : 0 < inner ℝ d (A d) := by nlinarith only [hh.1,hep,sq_pos_of_pos hp]
    exact hh'.ne'
  have hlineeq : -inner ℝ g d=alpha*inner ℝ d (A d) := by
    dsimp only [alpha,lineLength]
    rw [div_mul_cancel₀ _ hcurv,real_inner_comm]
  have hnorm : alpha*‖d‖=‖line‖ := by
    dsimp only [line]
    rw [P.line,norm_smul,Real.norm_eq_abs,abs_of_pos P.alpha]
  have hg := (observable_rfc_sharp_direction base hb f G x₀ B epsilon bar m ratio I hn
    hsize.le he hbar0.le hsmall hbar hm hr hlower hupper hsharp).2 A alpha hA P.alpha hlineeq
  rw [hnorm] at hg
  have hgradline : observableRFCLineGradient T f G r x₀ B=g+A line := by
    rw [P.searched]
    change searchedGradient g d (A d)=g+A line
    dsimp only [line]
    rw [P.line,map_smul]
    rfl
  have hnline : ‖observableRFCLineGradient T f G r x₀ B‖≤
      4*ratio^2*(4*R+‖line‖)+(9/8:ℝ)*‖line‖ := by
    rw [hgradline]
    exact (norm_add_le _ _).trans (add_le_add hg
      ((A.le_opNorm line).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg line))))
  have hshortline := observable_rfc_failed_line I P S.inverse_symmetric hn hsize he hbar0 hsmall hbar hfailed hshort
  have hlinebar : ‖line‖*bar≤16*R := (le_div_iff₀ hbar0).mp hshortline
  have hscaled := mul_le_mul_of_nonneg_right hnline hbar0.le
  have hshortscaled := mul_le_mul_of_nonneg_left hlinebar (show 0≤4*ratio^2+(9/8:ℝ) by positivity)
  have hfirst := mul_le_mul_of_nonneg_right hbp (show 0≤16*ratio^2*R by positivity)
  have hr2 : 1≤ratio^2 := by nlinarith only [hr,sq_nonneg (ratio-1)]
  have hR : 0≤R := norm_nonneg _
  have hlineg : ‖observableRFCLineGradient T f G r x₀ B‖≤(112*ratio^2/bar)*R := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hbar0).mpr
    change ‖observableRFCLineGradient T f G r x₀ B‖*bar≤112*ratio^2*R
    have ht : ‖observableRFCLineGradient T f G r x₀ B‖*bar≤65*ratio^2*R+18*R := by
      nlinarith only [hscaled,hshortscaled,hfirst]
    exact ht.trans (by nlinarith only [mul_le_mul_of_nonneg_right hr2 hR,hR])
  have hlocal : ‖T (rfcFunctionLinePoint T f fullMemory r x₀ B)‖≤r :=
    P.point.trans (by linarith only [hstart,S.radius_pos])
  have herror := S.gradient_error (T (rfcFunctionLinePoint T f fullMemory r x₀ B)) hlocal
  change ‖T (rfcFunctionLinePoint T f fullMemory r x₀ B)‖≤_
  have heq : coordinateGradient T G (T (rfcFunctionLinePoint T f fullMemory r x₀ B))=
      observableRFCLineGradient T f G r x₀ B := by
    simp only [coordinateGradient,T.symm_apply_apply,observableRFCLineGradient]
  rw [heq] at herror
  exact herror.trans ((mul_le_mul_of_nonneg_left hlineg (by norm_num)).trans_eq (by ring))

end
end krylov.Convergence
