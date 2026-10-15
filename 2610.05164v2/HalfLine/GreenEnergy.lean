import «2610.05164v2».HalfLine.GreenBounds

/-!
Article: 2610.05164v2, Theorem 3.3.
C.1's energy identity in the actual Sobolev norm.
Use: `«2610.05164v2».HalfLine.greenElement_energy` feeds
`«2610.05164v2».HalfLine.greenSolution_energy` (The literal half-line energy formula of C.1, for
arbitrary signed L1 data).
Proof chain: `«2610.05164v2».HalfLine.greenSolution_energy` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Zero extension of the half-line solution, as an actual H1 element.

Use: `«2610.05164v2».HalfLine.greenElement_energy` uses this definition to establish exact
identity `‖greenElement x j‖^2=∫ t in Iio x, j t*greenSolution x j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.
-/
def greenElement (x : ℝ) (j : ℝ → ℝ) : H1 :=
  (1/2:ℝ) • boundaryProjection x (convolution (leftDensity j x))

/--
Exact identity `H1.rep (boundaryProjection x u) t=H1.rep u t-exp (-|t-x|)*H1.rep u x`.

Use: `«2610.05164v2».HalfLine.greenElement_rep_left` rewrites with this identity to establish
exact identity `H1.rep (greenElement x j) t=greenSolution x j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_inner` with the arguments
shown in the proof.
-/
theorem boundaryProjection_rep_all (x : ℝ) (u : H1) (t : ℝ) :
    H1.rep (boundaryProjection x u) t=H1.rep u t-exp (-|t-x|)*H1.rep u x := by
  change (sqrt 2)⁻¹*inner ℝ (feature t)
    (u-inner ℝ (feature x) u • feature x)=_
  rw [inner_sub_right,real_inner_smul_right,feature_inner]
  change _=(sqrt 2)⁻¹*inner ℝ (feature t) u-exp (-|t-x|)*((sqrt 2)⁻¹*inner ℝ (feature x) u)
  ring

/--
Exact identity `H1.rep (greenElement x j) t=greenSolution x j t`.

Use: `«2610.05164v2».HalfLine.greenElement_energy` rewrites with this identity to establish
exact identity `‖greenElement x j‖^2=∫ t in Iio x, j t*greenSolution x j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.rep_smul`,
`«2610.05164v2».HalfLine.boundaryProjection_rep_all` with the arguments shown in the proof.
-/
theorem greenElement_rep_left {x t : ℝ} (j : ℝ → ℝ) (ht : t ≤ x) :
    H1.rep (greenElement x j) t=greenSolution x j t := by
  rw [greenElement,H1.rep_smul]
  change (1/2:ℝ)*H1.rep (boundaryProjection x (convolution (leftDensity j x))) t=_
  rw [boundaryProjection_rep_all,abs_of_nonpos (sub_nonpos.mpr ht),neg_neg]
  dsimp only [greenSolution]
  ring

/--
The precise assertion is `H1.rep (convolution (leftDensity j x)) t= exp (x-t)*H1.rep
(convolution (leftDensity j x)) x`.

Use: `«2610.05164v2».HalfLine.greenElement_rep_right` rewrites with this identity to establish
exact identity `H1.rep (greenElement x j) t=0`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Separate `z < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem convolution_leftDensity_right {j : ℝ → ℝ} (hj : Integrable j) {x t : ℝ} (ht : x ≤ t) :
    H1.rep (convolution (leftDensity j x)) t=
      exp (x-t)*H1.rep (convolution (leftDensity j x)) x := by
  -- Separate `z < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [convolution_rep (leftDensity_integrable hj x),convolution_rep (leftDensity_integrable hj x),
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    change exp (-|t-z|)*leftDensity j x z=exp (x-t)*(exp (-|x-z|)*leftDensity j x z)
    by_cases hz : z < x
    · rw [abs_of_nonneg (sub_nonneg.mpr (hz.le.trans ht)),abs_of_nonneg (sub_nonneg.mpr hz.le),
        ← mul_assoc (exp (x-t)), ← exp_add]
      have he : x-t+-(x-z)=-(t-z) := by ring
      rw [he]
    · simp [leftDensity,hz])

/--
Exact identity `H1.rep (greenElement x j) t=0`.

Use: `«2610.05164v2».HalfLine.greenElement_energy` uses this identity to establish exact
identity `‖greenElement x j‖^2=∫ t in Iio x, j t*greenSolution x j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.rep_smul`,
`«2610.05164v2».HalfLine.boundaryProjection_rep_all`,
`«2610.05164v2».HalfLine.convolution_leftDensity_right` with the arguments shown in the proof.
-/
theorem greenElement_rep_right {j : ℝ → ℝ} (hj : Integrable j) {x t : ℝ} (ht : x ≤ t) :
    H1.rep (greenElement x j) t=0 := by
  rw [greenElement,H1.rep_smul]
  change (1/2:ℝ)*H1.rep (boundaryProjection x (convolution (leftDensity j x))) t=0
  rw [boundaryProjection_rep_all,
    convolution_leftDensity_right hj ht,abs_of_nonneg (sub_nonneg.mpr ht)]
  have he : -(t-x)=x-t := by ring
  rw [he,sub_self,mul_zero]

/--
Exact identity `H1.rep (greenElement x j)=(Iio x).indicator (greenSolution x j)`.

Use: `«2610.05164v2».HalfLine.greenSolution_energy` rewrites with this identity to establish
the precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x, (greenSlope x
j t)^2+(greenSolution x j t)^2`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenElement_rep {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    H1.rep (greenElement x j)=(Iio x).indicator (greenSolution x j) := by
  funext t
  by_cases ht : t < x
  · rw [indicator_of_mem (show t ∈ Iio x from ht),greenElement_rep_left j ht.le]
  · rw [indicator_of_notMem (show t ∉ Iio x from ht),greenElement_rep_right hj (le_of_not_gt ht)]

/--
Exact identity `inner ℝ u (convolution j)=2*∫ t, j t*H1.rep u t`.

Use: `«2610.05164v2».HalfLine.greenElement_energy` rewrites with this identity to establish
exact identity `‖greenElement x j‖^2=∫ t in Iio x, j t*greenSolution x j t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem convolution_inner {j : ℝ → ℝ} (hj : Integrable j) (u : H1) :
    inner ℝ u (convolution j)=2*∫ t, j t*H1.rep u t := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [«2610.05164v2».GroundState.convolution,real_inner_smul_right, ← integral_inner (synthesisL1_integrable hj) u,
    ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change sqrt 2*inner ℝ u (j t • feature t)=2*(j t*H1.rep u t)
    rw [real_inner_smul_right]
    change sqrt 2*(j t*inner ℝ u (feature t))=2*(j t*((sqrt 2)⁻¹*inner ℝ (feature t) u))
    rw [real_inner_comm (feature t) u]
    have hs : sqrt 2^2=2 := sq_sqrt (by norm_num)
    field_simp
    linear_combination j t*inner ℝ (feature t) u*hs)

/--
C.1's energy identity in the actual Sobolev norm.

Exact identity `‖greenElement x j‖^2=∫ t in Iio x, j t*greenSolution x j t`.

Use: `«2610.05164v2».HalfLine.greenSolution_energy` rewrites with this identity to establish
the precise assertion is `(∫ t in Iio x, j t*greenSolution x j t)= ∫ t in Iio x, (greenSlope x
j t)^2+(greenSolution x j t)^2`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.greenSolution_energy`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenElement_energy {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    ‖greenElement x j‖^2=∫ t in Iio x, j t*greenSolution x j t := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let g := greenElement x j
  let U := convolution (leftDensity j x)
  have hboundary : inner ℝ (feature x) g=0 := by
    have he := greenElement_rep_right hj (le_refl x)
    change (sqrt 2)⁻¹*inner ℝ (feature x) g=0 at he
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero (sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne')
  have hinner : inner ℝ g (boundaryProjection x U)=inner ℝ g U := by
    change inner ℝ g (U-inner ℝ (feature x) U • feature x)=inner ℝ g U
    rw [inner_sub_right,real_inner_smul_right,real_inner_comm (feature x) g,hboundary,mul_zero,sub_zero]
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ g ((1/2:ℝ) • boundaryProjection x U)=_
  rw [real_inner_smul_right,hinner,convolution_inner (leftDensity_integrable hj x)]
  have he : (fun t => leftDensity j x t*H1.rep g t)=
      (Iio x).indicator (fun t => j t*greenSolution x j t) := by
    funext t
    by_cases ht : t < x
    · rw [leftDensity,indicator_of_mem (show t ∈ Iio x from ht),indicator_of_mem (show t ∈ Iio x from ht)]
      rw [show H1.rep g t=greenSolution x j t from greenElement_rep_left j ht.le]
    · simp [leftDensity,ht]
  rw [he,integral_indicator measurableSet_Iio]
  ring

end
end «2610.05164v2».HalfLine
