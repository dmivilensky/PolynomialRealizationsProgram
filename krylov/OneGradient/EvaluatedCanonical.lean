import krylov.Methods.EvaluatedGeometry
import krylov.OneGradient.XRFCProjector
import krylov.Reference.EnergyPositive
import krylov.Correction.TerminalCGResponse
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch(a), actual evaluated canonical launch.
Use: identify the original evaluated-point error and its true transported
step flags with the genuine CG error sum and orthogonal CG projections.
Source: executed evaluated-launch geometry, true canonical CG energy and
exact diagonal invariance of transported prefix selectors.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- The relative actual trial error from the evaluated point of the genuine
projection procedure; its exact evaluated length is the true CG length.
Use: original classical/evaluated source notation refers to real observations.
Article: main_krylov, prop:classical(a) and prop:launch(a). -/
def evaluatedTrialError (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  1-trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)/
    CG.length (cgOperator base) g i

/-- The original actual chronological evaluated-step matrix in canonical
physical coordinates.
Use: the source projectors are derived from these true executed columns.
Article: main_krylov, prop:launch(a). -/
def evaluatedCanonicalColumns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  metricRoot base*(show Matrix (Fin n) (Fin n) ℝ from fun a j =>
    (oneGradientStep (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g j.val) a)

/-- The actual canonical evaluated-point error is the complete negative
sum of genuine measured relative misses times the true energy unit steps.
Use: this is the original evaluated launch e, not an assumed surrogate vector.
Article: main_krylov, prop:launch(a).
Proof: true quadratic semantics and actual CG termination identify the
canonical gradient with the root-weighted physical evaluated-point error.
Apply the real accumulated trajectory identity and the true missed-line dictionary. -/
theorem evaluated_canonical_error (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g n
    cgOperator (metricRoot base)⁻¹ H.gradient=
      -(∑ i∈Finset.range n,(evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i)) •
        canonicalCGUnitStep base g i) := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => cgOperator base) g n
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  have hzero : g+cgOperator base (CG.displacement (cgOperator base) g n)=0 := by
    rw [← CG.gradient_displacement]
    have h := cg_terminates base hb g
    rwa [hc] at h
  have hgrad : H.gradient=cgOperator base (H.displacement-CG.displacement (cgOperator base) g n) := by
    calc
      _ = g+cgOperator base H.displacement := oneGradientRun_quadratic_gradient method _ g n
      _ = -cgOperator base (CG.displacement (cgOperator base) g n)+cgOperator base H.displacement :=
        congrArg (fun v => v+cgOperator base H.displacement) (eq_neg_of_add_eq_zero_left hzero)
      _ = _ := by rw [map_sub];abel
  have hpoint := evaluated_launch_displacement trial (cgOperator base) hp.1 hp.2 g n hpre ht n le_rfl
  have he : H.displacement-CG.displacement (cgOperator base) g n=
      -(∑ i∈Finset.range n,(CG.length (cgOperator base) g i-
        trial (oneGradientRun method (fun _ => cgOperator base) g i)) • CG.direction (cgOperator base) g i) := by
    rw [hpoint]
    abel
  change cgOperator (metricRoot base)⁻¹ H.gradient=_
  have hcan : cgOperator (metricRoot base)⁻¹
      (cgOperator base (H.displacement-CG.displacement (cgOperator base) g n))=
        cgOperator (metricRoot base) (H.displacement-CG.displacement (cgOperator base) g n) :=
    canonical_reference_action base hb _
  rw [hgrad,hcan,he,map_neg,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  have hic : i<referenceAtomCount base hb g := by omega
  rw [canonical_missed_line base hb g i hic]
  have ha := (cgLength_pos base hb g i hic).ne'
  congr 1
  rw [evaluatedTrialError,sub_div,div_self ha]

/-- Nonzero diagonal rescaling leaves the true transported prefix flag
unchanged, also for arbitrary nondiagonal physical bases.
Use: derive evaluated-launch flags from actual scaled CG columns.
Article: main_krylov, prop:launch(a).
Proof: the true diagonal commutes with the prefix selector; its actual
inverse cancels after the genuine product-inverse identity. -/
theorem transportedFlag_right_diagonal (V : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (hb : ∀ i,b i≠0) (l : ℕ) :
    transportedFlag (V*diagonal b) l=transportedFlag V l := by
  let D := diagonal b
  have hD : IsUnit D.det := by
    rw [Matrix.det_diagonal,isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  have hcomm : D*prefixProjection n l=prefixProjection n l*D := by
    simp only [D,prefixProjection,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  change (V*D)*prefixProjection n l*(V*D)⁻¹=V*prefixProjection n l*V⁻¹
  rw [Matrix.mul_inv_rev]
  calc
    _ = V*(D*prefixProjection n l)*(D⁻¹*V⁻¹) := by noncomm_ring
    _ = V*(prefixProjection n l*D)*(D⁻¹*V⁻¹) := by rw [hcomm]
    _ = V*prefixProjection n l*(D*D⁻¹)*V⁻¹ := by noncomm_ring
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hD,Matrix.mul_one]

/-- The actual canonical evaluated columns are the true unit CG frame
times their genuine nonzero diagonal trial/energy scales.
Use: the evaluated-prefix flags follow from real recorded steps.
Article: main_krylov, prop:launch(a).
Proof: the actual evaluated step is its true trial times the actual CG
direction, whose root image is its genuine normalized energy column. -/
theorem evaluated_canonical_columns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0) :
    evaluatedCanonicalColumns trial base g=canonicalCGUnitMatrix base g*diagonal (fun i : Fin n =>
      trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i.val)/
        CG.length (cgOperator base) g i.val*Real.sqrt (cgEnergy base g i.val)) := by
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by omega)
  ext a i
  rw [Matrix.mul_diagonal]
  have hs := evaluated_launch_step trial (cgOperator base) hp.1 hp.2 g n hpre ht i.val i.isLt.le
  have he : WithLp.toLp 2 (fun a => evaluatedCanonicalColumns trial base g a i)=
      cgOperator (metricRoot base) (oneGradientStep (evaluatedLaunchMethod trial)
        (fun _ => cgOperator base) g i.val) := rfl
  rw [oneGradientStep,hs,canonical_missed_line base hb g i.val (by omega)] at he
  simpa only [canonicalCGUnitMatrix,PiLp.smul_apply,smul_eq_mul,mul_comm] using
    congrArg (fun v : EuclideanSpace ℝ (Fin n) => v a) he

/-- The original actual evaluated-launch transported flags are exactly the
true orthogonal CG prefix projections.
Use: closes the source Pi_l=P_l geometry from the real implementation.
Article: main_krylov, prop:launch(a).
Proof: the actual canonical columns have nonzero diagonal CG scales, so the
proved diagonal invariance and genuine CG projection dictionary apply. -/
theorem evaluated_canonical_flags (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) : cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)=
      (oldFlag base g l).starProjection := by
  rw [evaluated_canonical_columns trial base hb g hc ht,transportedFlag_right_diagonal]
  · exact krylov.Correction.canonicalCG_transportedFlag base hb g hc l
  · intro i
    exact mul_ne_zero (div_ne_zero (ht i.val i.isLt)
      (cgLength_pos base hb g i.val (by omega)).ne')
        (Real.sqrt_pos.mpr (cgEnergy_pos base hb g i.val (by omega))).ne'

end
end krylov.OneGradient
