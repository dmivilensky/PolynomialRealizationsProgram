import «2610.05164v2».HalfLine.Resolvent
import «2610.05164v2».HalfLine.AtomicMeasure
import «2610.05164v2».StateRegion.ArticleCoordinates

/-!
Article: 2610.05164v2, Theorem 3.3.
The common spectral probability measure of C.1, constructed from the actual half-line operator.
Use: `«2610.05164v2».HalfLine.commonMeasure_response` feeds
`«2610.05164v2».HalfLine.commonMeasure_filter` (Theorem 3.3, with one actual measure for every
positive scale).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_filter` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ)

/--
Defines `positiveResolvent` of type `FeatureSpace →L[ℝ] FeatureSpace` by `inverseOfUnit
(ContinuousLinearMap.id ℝ FeatureSpace+s • operator hm hn x) (positive_pencil_unit
(operator_positive hm hn x) hs)`.

Use: `«2610.05164v2».HalfLine.responseQuadratic` uses this definition in the displayed
construction of `responseQuadratic`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.
-/
def positiveResolvent (s : ℝ) (hs : 0 ≤ s) : FeatureSpace →L[ℝ] FeatureSpace :=
  inverseOfUnit (ContinuousLinearMap.id ℝ FeatureSpace+s • operator hm hn x)
    (positive_pencil_unit (operator_positive hm hn x) hs)

include G in
/--
The precise assertion is `IsUnit (ContinuousLinearMap.id ℝ FeatureSpace+ (-groundParameter hm
hn) • operator hm hn x)`.

Use: `«2610.05164v2».HalfLine.groundQuadratic_hasSum` uses this assertion to establish the
infinite-sum formula stated in that declaration.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.ground_pencil_unit` with the
arguments shown in the proof.
-/
theorem ground_pencil_add_unit : IsUnit (ContinuousLinearMap.id ℝ FeatureSpace+
    (-groundParameter hm hn) • operator hm hn x) := by
  rw [neg_smul (groundParameter hm hn) (operator hm hn x),← sub_eq_add_neg]
  exact ground_pencil_unit G x

/--
Defines `groundResolvent` of type `FeatureSpace →L[ℝ] FeatureSpace` by `inverseOfUnit _
(ground_pencil_add_unit G x)`.

Use: `«2610.05164v2».HalfLine.groundQuadratic` uses this definition in the displayed
construction of `groundQuadratic`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def groundResolvent : FeatureSpace →L[ℝ] FeatureSpace :=
  inverseOfUnit _ (ground_pencil_add_unit G x)

/--
Defines `groundQuadratic` of type `ℝ` by `groundParameter hm hn* inner ℝ (vector hm hn x)
(groundResolvent G x (vector hm hn x))`.

Use: `«2610.05164v2».HalfLine.commonMeasure_response` rewrites with this definition to
establish the precise assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure
G x)= groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s
hs`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def groundQuadratic : ℝ := groundParameter hm hn*
  inner ℝ (vector hm hn x) (groundResolvent G x (vector hm hn x))

/--
Defines `responseQuadratic` of type `ℝ` by `inner ℝ (vector hm hn x) (positiveResolvent (hm :=
hm) (hn := hn) x s hs (vector hm hn x))`.

Use: `«2610.05164v2».HalfLine.commonMeasure_response` uses this definition to establish the
precise assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x)=
groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s hs`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.
-/
def responseQuadratic (s : ℝ) (hs : 0 ≤ s) : ℝ :=
  inner ℝ (vector hm hn x) (positiveResolvent (hm := hm) (hn := hn) x s hs (vector hm hn x))

include G in
/--
The stated quantitative bound `0 < 1-groundParameter hm hn*(spectralData hm hn x).eig i`.

Use: `«2610.05164v2».HalfLine.commonMeasure_response` uses this bound to establish the precise
assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x)= groundParameter
hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s hs`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Separate `0 < D.eig i` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem spectral_den_pos (i : (spectralData hm hn x).Index) :
    0 < 1-groundParameter hm hn*(spectralData hm hn x).eig i := by
  -- Separate `0 < D.eig i` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let D := spectralData hm hn x
  by_cases hi : 0 < D.eig i
  · have hf : D.basis i ≠ 0 := by
      intro h
      have hnorm := D.basis.orthonormal.norm_eq_one i
      rw [h,norm_zero] at hnorm
      norm_num at hnorm
    have he := eigenvalue_strict G x hf hi (D.equation i)
    have hmul := (lt_div_iff₀ G.coupling_positive).mp he
    change 0 < 1-groundParameter hm hn*D.eig i
    nlinarith
  · have hz : D.eig i=0 := le_antisymm (le_of_not_gt hi) (D.nonneg i)
    change 0 < 1-groundParameter hm hn*D.eig i
    rw [hz]
    norm_num

/--
The value of a convergent infinite sum: `HasSum (fun i : (spectralData hm hn x).Index =>
groundParameter hm hn* (inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2/
(1-groundParameter hm hn*(spectralData hm hn x).eig i)) (groundQuadratic G x)`.

Use: `«2610.05164v2».HalfLine.probabilityWeight_hasSum` uses this infinite-sum formula to
establish the value of a convergent infinite sum: `HasSum (probabilityWeight G x) 1`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.ground_pencil_add_unit`,
`«2610.05164v2».HalfLine.resolvent_quadratic_hasSum`,
`«2610.05164v2».HalfLine.operator_positive` with the arguments shown in the proof.
-/
theorem groundQuadratic_hasSum :
    HasSum (fun i : (spectralData hm hn x).Index => groundParameter hm hn*
      (inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2/
      (1-groundParameter hm hn*(spectralData hm hn x).eig i)) (groundQuadratic G x) := by
  -- Use the identities/estimates `«2610.05164v2».HalfLine.ground_pencil_add_unit`,
  -- `«2610.05164v2».HalfLine.resolvent_quadratic_hasSum`,
  -- `«2610.05164v2».HalfLine.operator_positive` with the arguments shown in the proof.
  have h := (resolvent_quadratic_hasSum (spectralData hm hn x) (operator_positive hm hn x)
    (-groundParameter hm hn) (ground_pencil_add_unit G x) (fun i => by
      simpa only [neg_mul,sub_eq_add_neg] using (spectral_den_pos G x i).ne') (vector hm hn x)).mul_left
      (groundParameter hm hn)
  simpa only [groundQuadratic,groundResolvent,neg_mul,← sub_eq_add_neg,mul_div_assoc] using h

/--
The value of a convergent infinite sum: `HasSum (fun i : (spectralData hm hn x).Index => (inner
ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2/ (1+s*(spectralData hm hn x).eig i))
(responseQuadratic (hm := hm) (hn := hn) x s hs)`.

Use: `«2610.05164v2».HalfLine.commonMeasure_response` uses this infinite-sum formula to
establish the precise assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure
G x)= groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s
hs`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.resolvent_quadratic_hasSum`,
`«2610.05164v2».HalfLine.operator_positive`, `«2610.05164v2».HalfLine.positive_pencil_unit`
with the arguments shown in the proof.
-/
theorem responseQuadratic_hasSum (s : ℝ) (hs : 0 ≤ s) :
    HasSum (fun i : (spectralData hm hn x).Index =>
      (inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2/
        (1+s*(spectralData hm hn x).eig i)) (responseQuadratic (hm := hm) (hn := hn) x s hs) :=
  resolvent_quadratic_hasSum (spectralData hm hn x) (operator_positive hm hn x) s
    (positive_pencil_unit (operator_positive hm hn x) hs)
    (fun i => ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hs ((spectralData hm hn x).nonneg i)))) (vector hm hn x)

/--
Defines `probabilityWeight` of type `ℝ` by `(groundParameter hm hn*(inner ℝ ((spectralData hm
hn x).basis i) (vector hm hn x))^2/ (1-groundParameter hm hn*(spectralData hm hn x).eig
i))/groundQuadratic G x`.

Use: `«2610.05164v2».HalfLine.commonMeasure` uses this definition in the displayed construction
of `commonMeasure`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def probabilityWeight (i : (spectralData hm hn x).Index) : ℝ :=
  (groundParameter hm hn*(inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2/
    (1-groundParameter hm hn*(spectralData hm hn x).eig i))/groundQuadratic G x

/--
Defines `commonMeasure` of type `Measure ℝ` by `atomicMeasure (probabilityWeight G x) (fun i =>
groundParameter hm hn*(spectralData hm hn x).eig i)`.

Use: `«2610.05164v2».HalfLine.commonMeasure_response` rewrites with this definition to
establish the precise assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure
G x)= groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s
hs`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def commonMeasure : Measure ℝ := atomicMeasure (probabilityWeight G x)
  (fun i => groundParameter hm hn*(spectralData hm hn x).eig i)

/--
The stated quantitative bound `0 ≤ probabilityWeight G x i`.

Use: `«2610.05164v2».HalfLine.commonMeasure_probability` uses this bound to establish the
precise assertion is `IsProbabilityMeasure (commonMeasure G x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coupling_positive`,
`«2610.05164v2».HalfLine.spectral_den_pos` with the arguments shown in the proof.
-/
theorem probabilityWeight_nonneg (hq : 0 < groundQuadratic G x)
    (i : (spectralData hm hn x).Index) : 0 ≤ probabilityWeight G x i :=
  div_nonneg (div_nonneg (mul_nonneg G.coupling_positive.le (sq_nonneg _))
    (spectral_den_pos G x i).le) hq.le

/--
The value of a convergent infinite sum: `HasSum (probabilityWeight G x) 1`.

Use: `«2610.05164v2».HalfLine.commonMeasure_probability` uses this infinite-sum formula to
establish the precise assertion is `IsProbabilityMeasure (commonMeasure G x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.groundQuadratic_hasSum` with the
arguments shown in the proof.
-/
theorem probabilityWeight_hasSum (hq : 0 < groundQuadratic G x) :
    HasSum (probabilityWeight G x) 1 := by
  have h := (groundQuadratic_hasSum G x).div_const (groundQuadratic G x)
  change HasSum (fun i => (groundParameter hm hn*
    (inner ℝ ((spectralData hm hn x).basis i) (vector hm hn x))^2/
    (1-groundParameter hm hn*(spectralData hm hn x).eig i))/groundQuadratic G x) 1
  simpa only [div_self hq.ne'] using h

/--
The precise assertion is `IsProbabilityMeasure (commonMeasure G x)`.

Use: `«2610.05164v2».HalfLine.commonMeasure_mean` uses this assertion to establish exact
identity `(∫ z, z ∂commonMeasure G x)=1-Filters.linear hm hn x/groundQuadratic G x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.atomicMeasure_probability`,
`«2610.05164v2».HalfLine.probabilityWeight_nonneg`,
`«2610.05164v2».HalfLine.probabilityWeight_hasSum` with the arguments shown in the proof.
-/
theorem commonMeasure_probability (hq : 0 < groundQuadratic G x) :
    IsProbabilityMeasure (commonMeasure G x) :=
  atomicMeasure_probability (probabilityWeight_nonneg G x hq) (probabilityWeight_hasSum G x hq)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ z ∂commonMeasure G x, z ∈
Ico (0:ℝ) 1`.

Use: `«2610.05164v2».HalfLine.commonMeasure_mean` uses this assertion to establish exact
identity `(∫ z, z ∂commonMeasure G x)=1-Filters.linear hm hn x/groundQuadratic G x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_defect`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.orthonormal_countable`,
`«2610.05164v2».HalfLine.atomicMeasure_supported`,
`«2610.05164v2».GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem commonMeasure_supported : ∀ᵐ z ∂commonMeasure G x, z ∈ Ico (0:ℝ) 1 := by
  let D := spectralData hm hn x
  let : Countable D.Index := orthonormal_countable D.basis.orthonormal
  apply atomicMeasure_supported measurableSet_Ico
  intro i
  exact ⟨mul_nonneg G.coupling_positive.le (D.nonneg i),by
    have h := spectral_den_pos G x i
    linarith⟩

/--
A single measure represents every nonnegative scale, including s=0.

The precise assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x)=
groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s hs`.

Use: `«2610.05164v2».HalfLine.commonMeasure_filter` rewrites with this identity to establish
the precise assertion is `groundParameter hm hn*Filters.nonlinear s m x/(s*G.q x)= ∫ z,
(1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem commonMeasure_response (hq : 0 < groundQuadratic G x) (s : ℝ) (hs : 0 ≤ s) :
    (∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x)=
      groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s hs := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let D := spectralData hm hn x
  let : Countable D.Index := orthonormal_countable D.basis.orthonormal
  rw [commonMeasure,atomicMeasure_integral (probabilityWeight_nonneg G x hq)]
  have he (i : D.Index) : probabilityWeight G x i*
      ((1-groundParameter hm hn*D.eig i)/(1+(s/groundParameter hm hn)*(groundParameter hm hn*D.eig i)))=
      (groundParameter hm hn/groundQuadratic G x)*
        ((inner ℝ (D.basis i) (vector hm hn x))^2/(1+s*D.eig i)) := by
    have hd := (spectral_den_pos G x i).ne'
    have hsd : 1+s*D.eig i ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hs (D.nonneg i)))
    dsimp only [probabilityWeight]
    change _=_
    field_simp [G.coupling_positive.ne',hd,hsd,hq.ne']
    dsimp only [D]
    ring
  change (∑' i : D.Index, probabilityWeight G x i*
    ((1-groundParameter hm hn*D.eig i)/(1+(s/groundParameter hm hn)*(groundParameter hm hn*D.eig i))))=_
  rw [show (fun i : D.Index => probabilityWeight G x i*
    ((1-groundParameter hm hn*D.eig i)/(1+(s/groundParameter hm hn)*(groundParameter hm hn*D.eig i))))=
    (fun i => (groundParameter hm hn/groundQuadratic G x)*
      ((inner ℝ (D.basis i) (vector hm hn x))^2/(1+s*D.eig i))) from funext he]
  exact ((responseQuadratic_hasSum (hm := hm) (hn := hn) x s hs).mul_left
    (groundParameter hm hn/groundQuadratic G x)).tsum_eq

end
end «2610.05164v2».HalfLine
