import «2610.05164v2».Numerics.JetExpr
import «2610.05164v2».DualCertificate.RationalReference
import «2610.05164v2».DualCertificate.ReferenceFilters

/-!
Article: 2610.05164v2, Section 4.1.
The literal reference coefficient provider of F.1(R).
Use: `«2610.05164v2».Numerics.ReferenceJetSource.referenceData` feeds
`«2610.05164v2».Certificates.Compact.ContactValues.contact_integral_enclosed` (contact integral
enclosed).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core «2610.05164v2».DualCertificate
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace JetExpr
/--
Defines `cube` of type `JetExpr` by `.mul (.square e) e`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.Q` uses this definition in the displayed
construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def cube (e : JetExpr) : JetExpr := .mul (.square e) e
/--
Defines `scale` of type `JetExpr` by `.mul (.literal q) e`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.A` uses this definition in the displayed
construction of `A`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def scale (q : ℚ) (e : JetExpr) : JetExpr := .mul (.literal q) e
/--
Defines `sum` by pattern matching with result type `List JetExpr → JetExpr`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Numerics.JetExpr.sum_value` rewrites with this definition to establish
exact identity `(sum es).value t=(es.map (fun e => e.value t)).sum`.

Article: 2610.05164v2, Section 4.1.
-/
def sum : List JetExpr → JetExpr
  | [] => .literal 0
  | e::es => .add e (sum es)

/--
Exact identity `(sum es).value t=(es.map (fun e => e.value t)).sum`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.p_value` rewrites with this identity to
establish exact identity `(p R W).value t=R.coefficient (t^3*(2-t^3))`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `es`; the recursive step uses the previous-stage assertion.
-/
theorem sum_value (es : List JetExpr) (t : ℝ) :
    (sum es).value t=(es.map (fun e => e.value t)).sum := by
  induction es with
  | nil => simp [sum,value]
  | cons e es ih => simp [sum,value,ih]

/--
The precise assertion is `(sum es).Regular s`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.p_regular` uses this assertion to establish
the precise assertion is `(p R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Induct on `es`; the recursive step uses the previous-stage assertion.
-/
theorem sum_regular {s : Set ℝ} {es : List JetExpr}
    (h : ∀ e∈es,e.Regular s) : (sum es).Regular s := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun a ha => h a (by simp [ha]))⟩
end JetExpr

namespace ReferenceJetSource
variable (R : RationalReference) (W : ℕ → IntervalJet)

/--
Defines `k` of type `JetExpr` by `.scale (1/4) (.square .pi)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.C` uses this definition in the displayed
construction of `C`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def k : JetExpr := .scale (1/4) (.square .pi)
/--
Defines `h` of type `JetExpr` by `.add (.literal 2) (.neg (.cube .variable))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.Q` uses this definition in the displayed
construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def h : JetExpr := .add (.literal 2) (.neg (.cube .variable))
/--
Defines `Q` of type `JetExpr` by `.mul (.cube .variable) h`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.Q_value` rewrites with this definition to
establish exact identity `Q.value t=t^3*(2-t^3)`.

Article: 2610.05164v2, Section 4.1.
-/
def Q : JetExpr := .mul (.cube .variable) h
/--
Defines `term` of type `JetExpr` by `.scale (R.p i) (.mul Q (.inverse (.add Q (.literal (R.ζ
i))) (W i)))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.p` uses this definition in the displayed
construction of `p`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def term (i : Fin R.count) : JetExpr :=
  .scale (R.p i) (.mul Q (.inverse (.add Q (.literal (R.ζ i))) (W i)))
/--
Defines `p` of type `JetExpr` by `.enclosed (.add (.literal R.p₀) (.sum (List.ofFn (term R
W)))) (W (R.count+4))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.beta` uses this definition in the displayed
construction of `beta`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def p : JetExpr := .enclosed (.add (.literal R.p₀) (.sum (List.ofFn (term R W)))) (W (R.count+4))
/--
Defines `inverseK` of type `JetExpr` by `.inverse k (W R.count)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.alpha` uses this definition in the displayed
construction of `alpha`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def inverseK : JetExpr := .inverse k (W R.count)
/--
Defines `alpha` of type `JetExpr` by `.enclosed (.scale 3 (.mul (.mul .variable h) (inverseK R
W))) (W (R.count+5))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.alpha_value` rewrites with this definition to
establish exact identity `(alpha R W).value t=3*(t*(2-t^3))/(Real.pi^2/4)`.

Article: 2610.05164v2, Section 4.1.
-/
def alpha : JetExpr := .enclosed (.scale 3 (.mul (.mul .variable h) (inverseK R W))) (W (R.count+5))
/--
Defines `beta` of type `JetExpr` by `.enclosed (.scale 2 (.mul (.mul (p R W) h) (inverseK R
W))) (W (R.count+6))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.beta_value` rewrites with this definition to
establish exact identity `(beta R W).value t=2*R.coefficient
(t^3*(2-t^3))*(2-t^3)/(Real.pi^2/4)`.

Article: 2610.05164v2, Section 4.1.
-/
def beta : JetExpr := .enclosed (.scale 2 (.mul (.mul (p R W) h) (inverseK R W))) (W (R.count+6))
/--
Defines `root` of type `JetExpr` by `.cubic (alpha R W) (beta R W) (W (R.count+1))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.amplitude` uses this definition in the
displayed construction of `amplitude`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Section 4.1.
-/
def root : JetExpr := .cubic (alpha R W) (beta R W) (W (R.count+1))
/--
Defines `speed` of type `JetExpr` by `.enclosed (.add (.scale 2 (.mul .variable h)) (.scale 2
(.mul (.mul (p R W) h) (.inverse (root R W) (W (R.count+2)))))) (W (R.count+7))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.speed_value` rewrites with this definition to
establish exact identity `(speed R W).value t=(referenceData R).normalizedSpeed t`.

Article: 2610.05164v2, Section 4.1.
-/
def speed : JetExpr := .enclosed (.add (.scale 2 (.mul .variable h))
  (.scale 2 (.mul (.mul (p R W) h) (.inverse (root R W) (W (R.count+2)))))) (W (R.count+7))
/--
Defines `velocity` of type `JetExpr` by `.enclosed (.scale 3 (.inverse (speed R W) (W
(R.count+3)))) (W (R.count+8))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.A` uses this definition in the displayed
construction of `A`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def velocity : JetExpr := .enclosed (.scale 3 (.inverse (speed R W) (W (R.count+3)))) (W (R.count+8))
/--
Defines `amplitude` of type `JetExpr` by `.enclosed (.mul .variable (root R W)) (W
(R.count+9))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.C` uses this definition in the displayed
construction of `C`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Section 4.1.
-/
def amplitude : JetExpr := .enclosed (.mul .variable (root R W)) (W (R.count+9))
/--
Defines `C` of type `JetExpr` by `.mul (.mul (velocity R W) k) (.square (amplitude R W))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this definition to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
def C : JetExpr := .mul (.mul (velocity R W) k) (.square (amplitude R W))
/--
Defines `A` of type `JetExpr` by `.scale (-2) (velocity R W)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this definition to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
def A : JetExpr := .scale (-2) (velocity R W)
/--
Defines `B` of type `JetExpr` by `.scale (-sigma) (velocity R W)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this definition to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Section 4.1.
-/
def B (sigma : ℚ) : JetExpr := .scale (-sigma) (velocity R W)

/--
Defines `referenceData` of type `«2610.05164v2».Calibration.ReferenceData` by `R.referenceData
(k := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this definition to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
noncomputable def referenceData : «2610.05164v2».Calibration.ReferenceData :=
  R.referenceData (k := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))

/--
Exact identity `k.value t=Real.pi^2/4`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this identity to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem k_value (t : ℝ) : k.value t=Real.pi^2/4 := by
  simp only [k,JetExpr.scale,JetExpr.value,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  ring

/--
Exact identity `h.value t=2-t^3`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.Q_value` rewrites with this identity to
establish exact identity `Q.value t=t^3*(2-t^3)`.

Article: 2610.05164v2, Section 4.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem h_value (t : ℝ) : h.value t=2-t^3 := by simp only [h,JetExpr.cube,JetExpr.value,Rat.cast_ofNat]; ring

/--
Exact identity `Q.value t=t^3*(2-t^3)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.p_regular` rewrites with this identity to
establish the precise assertion is `(p R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.h_value` with
the arguments shown in the proof.
-/
theorem Q_value (t : ℝ) : Q.value t=t^3*(2-t^3) := by simp only [Q,JetExpr.cube,JetExpr.value,h_value]; ring

/--
Exact identity `(p R W).value t=R.coefficient (t^3*(2-t^3))`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.beta_value` rewrites with this identity to
establish exact identity `(beta R W).value t=2*R.coefficient
(t^3*(2-t^3))*(2-t^3)/(Real.pi^2/4)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.sum_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.Q_value` with the arguments shown in the proof.
-/
theorem p_value (t : ℝ) : (p R W).value t=R.coefficient (t^3*(2-t^3)) := by
  simp only [p,JetExpr.value,JetExpr.sum_value,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    term,JetExpr.scale,Q_value,RationalReference.coefficient,div_eq_mul_inv,mul_assoc]

/--
Exact identity `(inverseK R W).value t=(Real.pi^2/4)⁻¹`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.alpha_value` rewrites with this identity to
establish exact identity `(alpha R W).value t=3*(t*(2-t^3))/(Real.pi^2/4)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.k_value` with
the arguments shown in the proof.
-/
theorem inverseK_value (t : ℝ) : (inverseK R W).value t=(Real.pi^2/4)⁻¹ := by simp only [inverseK,JetExpr.value,k_value]

/--
Exact identity `(alpha R W).value t=3*(t*(2-t^3))/(Real.pi^2/4)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.root_regular` rewrites with this identity to
establish the precise assertion is `(root R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.h_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.inverseK_value` with the arguments shown in the
proof.
-/
theorem alpha_value (t : ℝ) :
    (alpha R W).value t=3*(t*(2-t^3))/(Real.pi^2/4) := by
  simp only [alpha,JetExpr.scale,JetExpr.value,h_value,inverseK_value,Rat.cast_ofNat,div_eq_mul_inv]
  ring

/--
Exact identity `(beta R W).value t=2*R.coefficient (t^3*(2-t^3))*(2-t^3)/(Real.pi^2/4)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.root_regular` rewrites with this identity to
establish the precise assertion is `(root R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.p_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.h_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.inverseK_value` with the arguments shown in the
proof.
-/
theorem beta_value (t : ℝ) :
    (beta R W).value t=2*R.coefficient (t^3*(2-t^3))*(2-t^3)/(Real.pi^2/4) := by
  simp only [beta,JetExpr.scale,JetExpr.value,p_value,h_value,inverseK_value,Rat.cast_ofNat,div_eq_mul_inv]
  ring

/--
Exact identity `(root R W).value t=(referenceData R).normalizedRoot t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this identity to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Section 4.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem root_value {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (root R W).value t=(referenceData R).normalizedRoot t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hc := «2610.05164v2».DualCertificate.cube_mem ht
  have hp := R.coefficient_positive («2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem ht).1
  have hk : 0<Real.pi^2/4 := div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)
  have hr := (referenceData R).normalizedRoot_spec ht
  simp only [root,JetExpr.value,alpha_value,beta_value]
  apply positiveCubic_unique (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg ht.1 (by linarith [hc.2]))) hk.le)
    (div_pos (mul_pos (mul_pos (by norm_num) hp) (by linarith [hc.2])) hk) hr.1
  have he := hr.2
  change (Real.pi^2/4)*(referenceData R).normalizedRoot t^3-
    3*(t*(2-t^3))*(referenceData R).normalizedRoot t-
    2*R.coefficient (t^3*(2-t^3))*(2-t^3)=0 at he
  field_simp [hk.ne']
  nlinarith [he]

/--
Exact identity `(speed R W).value t=(referenceData R).normalizedSpeed t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.velocity_regular` rewrites with this identity
to establish `(velocity R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.h_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.p_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.root_value` with the arguments shown in the proof.
-/
theorem speed_value {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (speed R W).value t=(referenceData R).normalizedSpeed t := by
  simp only [speed,JetExpr.scale,JetExpr.value,h_value,p_value,root_value R W ht,Rat.cast_ofNat,
    «2610.05164v2».Calibration.ReferenceData.normalizedSpeed,referenceData,RationalReference.referenceData]
  ring

/--
Exact identity `(velocity R W).value t=(referenceData R).normalizedVelocity t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.filter_ode` rewrites with this identity to
establish the derivative formula stated in that declaration.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.speed_value`
with the arguments shown in the proof.
-/
theorem velocity_value {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (velocity R W).value t=(referenceData R).normalizedVelocity t := by
  simp only [velocity,JetExpr.scale,JetExpr.value,speed_value R W ht,Rat.cast_ofNat,
    «2610.05164v2».Calibration.ReferenceData.normalizedVelocity,div_eq_mul_inv]

/--
The precise assertion is `(p R W).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.root_regular` uses this assertion to establish
the precise assertion is `(root R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.sum_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.Q_value`,
`«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem` with the arguments shown
in the proof.
-/
theorem p_regular : (p R W).Regular (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.JetExpr.sum_regular`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.Q_value`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem` with the arguments
  -- shown in the proof.
  constructor
  · trivial
  · apply JetExpr.sum_regular
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    refine ⟨trivial,⟨?_,⟨?_,?_⟩⟩⟩
    · simp only [Q,h,JetExpr.cube,JetExpr.Regular]; trivial
    · simp only [JetExpr.Regular,Q,h,JetExpr.cube]; trivial
    · intro t ht
      simp only [JetExpr.value,Q_value]
      have hz : (0:ℝ)<R.ζ i := by exact_mod_cast R.ζ_pos i
      have hQ := («2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem ht).1
      linarith

/--
The precise assertion is `(root R W).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.C_regular` uses this assertion to establish
the precise assertion is `(C R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.k_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.p_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.alpha_value` with the arguments shown in the proof.
-/
theorem root_regular : (root R W).Regular (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.k_value`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.p_regular`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.alpha_value` with the arguments shown in the
  -- proof.
  have hk : k.Regular (Icc (0:ℝ) 1) := by trivial
  have hinv : (inverseK R W).Regular (Icc (0:ℝ) 1) := by
    refine ⟨hk,fun t _ => ?_⟩
    rw [k_value]
    positivity
  have ht : JetExpr.variable.Regular (Icc (0:ℝ) 1) := trivial
  have hh : h.Regular (Icc (0:ℝ) 1) := by trivial
  refine ⟨⟨⟨trivial,⟨⟨ht,hh⟩,hinv⟩⟩,⟨trivial,⟨⟨p_regular R W,hh⟩,hinv⟩⟩⟩,?_,?_⟩
  · intro t ht
    rw [alpha_value]
    have hc := «2610.05164v2».DualCertificate.cube_mem ht
    exact div_nonneg (mul_nonneg (by norm_num) (mul_nonneg ht.1 (by linarith [hc.2]))) (by positivity)
  · intro t ht
    rw [beta_value]
    have hc := «2610.05164v2».DualCertificate.cube_mem ht
    exact div_pos (mul_pos (mul_pos (by norm_num)
      (R.coefficient_positive («2610.05164v2».Calibration.ReferenceData.normalized_coefficient_mem ht).1))
      (by linarith [hc.2])) (by positivity)

/--
The precise assertion is `(speed R W).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.velocity_regular` uses this assertion to
establish the precise assertion is `(velocity R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.p_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.root_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.root_value` with the arguments shown in the proof.
-/
theorem speed_regular : (speed R W).Regular (Icc (0:ℝ) 1) := by
  refine ⟨?_,⟨trivial,⟨⟨p_regular R W,?_⟩,⟨root_regular R W,?_⟩⟩⟩⟩
  · trivial
  · trivial
  · intro t ht
    rw [root_value R W ht]
    exact ((referenceData R).normalizedRoot_spec ht).1.ne'

/--
The precise assertion is `(velocity R W).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.A_regular` uses this assertion to establish
the precise assertion is `(A R W).Regular (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.speed_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.speed_value`,
`«2610.05164v2».Calibration.ReferenceData.normalizedSpeed_positive` with the arguments shown in
the proof.
-/
theorem velocity_regular : (velocity R W).Regular (Icc (0:ℝ) 1) := by
  refine ⟨trivial,⟨speed_regular R W,?_⟩⟩
  intro t ht
  rw [speed_value R W ht]
  exact ((referenceData R).normalizedSpeed_positive ht).ne'

/--
The precise assertion is `(C R W).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.coefficientC_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (coefficientC R) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.velocity_regular`,
`«2610.05164v2».Numerics.ReferenceJetSource.root_regular` with the arguments shown in the
proof.
-/
theorem C_regular : (C R W).Regular (Icc (0:ℝ) 1) :=
  ⟨⟨velocity_regular R W,by trivial⟩,⟨trivial,root_regular R W⟩⟩
/--
The precise assertion is `(A R W).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.coefficientA_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (coefficientA R) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.velocity_regular` with the arguments shown in the
proof.
-/
theorem A_regular : (A R W).Regular (Icc (0:ℝ) 1) := ⟨trivial,velocity_regular R W⟩
/--
The precise assertion is `(B R W sigma).Regular (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.coefficientB_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (coefficientB R sigma) (Icc (0:ℝ)
1)`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.velocity_regular` with the arguments shown in the
proof.
-/
theorem B_regular (sigma : ℚ) : (B R W sigma).Regular (Icc (0:ℝ) 1) :=
  ⟨trivial,velocity_regular R W⟩

/--
The derivative within the stated domain: `HasDerivWithinAt ((referenceData R).normalizedFilter
(σ := (sigma:ℝ)) (by exact_mod_cast hsigma)) ((C R W).value t+(A R W).value t*(referenceData
R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t+ (B R W sigma).value
t*((referenceData R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t)^2) (Icc
(0:ℝ) 1) t`.

Use: `«2610.05164v2».Numerics.ReferenceJetSource.actual_filter_step` uses this derivative
formula to establish membership in the specified domain/enclosure: `(referenceData
R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) ((a:ℝ)+W.width)∈W.output`.

Article: 2610.05164v2, Section 4.1.

Proof: Use the identities/estimates
`«2610.05164v2».Numerics.ReferenceJetSource.velocity_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.k_value`,
`«2610.05164v2».Numerics.ReferenceJetSource.root_value` with the arguments shown in the proof.
-/
theorem filter_ode {sigma : ℚ} (hsigma : 0<sigma) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt ((referenceData R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma))
      ((C R W).value t+(A R W).value t*(referenceData R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t+
        (B R W sigma).value t*((referenceData R).normalizedFilter (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) t)^2)
      (Icc (0:ℝ) 1) t := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.ReferenceJetSource.velocity_value`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.k_value`,
  -- `«2610.05164v2».Numerics.ReferenceJetSource.root_value` with the arguments shown in the
  -- proof.
  convert! (referenceData R).normalizedFilter_derivative (σ := (sigma:ℝ)) (by exact_mod_cast hsigma) ht using 1
  simp only [C,A,B,amplitude,JetExpr.scale,JetExpr.value,velocity_value R W ht,
    root_value R W ht,k_value,Rat.cast_neg,Rat.cast_ofNat,referenceData,RationalReference.referenceData]
  ring

end ReferenceJetSource
end «2610.05164v2».Numerics
