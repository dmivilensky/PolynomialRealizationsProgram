import «2610.05164v2».HalfLine.GreenSolution
import «2610.05164v2».Filters.Nonlinear

/-!
Article: 2610.05164v2, Theorem 3.3.
The ground coordinate as the left boundary flux of the actual ground state.
Use: `«2610.05164v2».HalfLine.ground_boundary_flux` feeds
`«2610.05164v2».HalfLine.groundQuadratic_eq_coordinate` (The missing analytic identification in
Theorem 3.3: q is the actual negative-scale resolvent quadratic form, not a newly defined
coordinate).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_ode_probability` — 2610.05164v2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Integrability of the displayed function: `Integrable (fun t => m t*H1.rep u t)`.

Use: `«2610.05164v2».HalfLine.densityOperator_rep_convolution` rewrites with this integrability
result to establish the identity `H1.rep (densityOperator m u) x=H1.rep (convolution (fun t
=> m t*H1.rep u t)) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.bounded_forcing_integrable`,
`«2610.05164v2».Sobolev.H1.continuous_rep`, `«2610.05164v2».Sobolev.H1.evaluation_bound` with
the arguments shown in the proof.
-/
theorem density_rep_forcing_integrable {m : ℝ → ℝ} (hm : Integrable m) (u : H1) :
    Integrable (fun t => m t*H1.rep u t) :=
  Filters.bounded_forcing_integrable hm (H1.continuous_rep u).aestronglyMeasurable
    (fun t => by simpa only [Real.norm_eq_abs] using H1.evaluation_bound u t)

/--
Exact identity `H1.rep (densityOperator m u) x=H1.rep (convolution (fun t => m t*H1.rep u t))
x`.

Use: `«2610.05164v2».HalfLine.ground_convolution` uses this identity to establish exact
identity `H1.rep G.u t=groundParameter hm hn/2* H1.rep (convolution (fun y => m y*H1.rep G.u
y)) t`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem densityOperator_rep_convolution {m : ℝ → ℝ} (hm : Integrable m) (u : H1) (x : ℝ) :
    H1.rep (densityOperator m u) x=H1.rep (convolution (fun t => m t*H1.rep u t)) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [convolution_rep (density_rep_forcing_integrable hm u)]
  change (sqrt 2)⁻¹*inner ℝ (feature x) (densityOperator m u)=_
  rw [densityOperator_inner hm, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change (sqrt 2)⁻¹*(m t*(inner ℝ (feature t) (feature x)*inner ℝ (feature t) u))=
      exp (-|x-t|)*(m t*((sqrt 2)⁻¹*inner ℝ (feature t) u))
    rw [feature_inner, abs_sub_comm t x]
    ring)

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t} (G : GroundWitness hm hn)
include G

/--
Exact identity `H1.rep G.u t=groundParameter hm hn/2* H1.rep (convolution (fun y => m y*H1.rep
G.u y)) t`.

Use: `«2610.05164v2».HalfLine.ground_boundary_flux` uses this identity to establish exact
identity `G.q x=groundParameter hm hn/H1.rep G.u x* leftGreen (fun y => m y*H1.rep G.u y) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ground_convolution (t : ℝ) :
    H1.rep G.u t=groundParameter hm hn/2*
      H1.rep (convolution (fun y => m y*H1.rep G.u y)) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he := densityOperator_rep_convolution hm G.u t
  rw [G.eigen, H1.rep_smul] at he
  change kernelEigenvalue hm hn 0*H1.rep G.u t=_ at he
  dsimp only [groundParameter]
  have hp := top_density_attained hm hn G.mass_positive |>.1
  field_simp
  nlinarith [he]

/--
Exact identity `G.d t=groundParameter hm hn/2*convolutionSlope (fun y => m y*H1.rep G.u y) t`.

Use: `«2610.05164v2».HalfLine.ground_boundary_flux` uses this identity to establish exact
identity `G.q x=groundParameter hm hn/H1.rep G.u x* leftGreen (fun y => m y*H1.rep G.u y) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ground_convolution_slope (t : ℝ) :
    G.d t=groundParameter hm hn/2*convolutionSlope (fun y => m y*H1.rep G.u y) t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hd := (convolution_hasDerivAt (density_rep_forcing_integrable hm G.u) t).const_mul
    (groundParameter hm hn/2)
  have he : (fun t => groundParameter hm hn/2*
      H1.rep (convolution (fun y => m y*H1.rep G.u y)) t)=H1.rep G.u :=
    funext (fun t => (ground_convolution G t).symm)
  change HasDerivAt (fun t => groundParameter hm hn/2*
    H1.rep (convolution (fun y => m y*H1.rep G.u y)) t)
    (groundParameter hm hn/2*convolutionSlope (fun y => m y*H1.rep G.u y) t) t at hd
  rw [he] at hd
  exact (G.derivative t).unique hd

/--
The ground coordinate as the left boundary flux of the actual ground state.

Exact identity `G.q x=groundParameter hm hn/H1.rep G.u x* leftGreen (fun y => m y*H1.rep G.u y)
x`.

Use: `«2610.05164v2».HalfLine.groundQuadratic_eq_coordinate` rewrites with this identity to
establish exact identity `groundQuadratic G x=G.q x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ground_boundary_flux (x : ℝ) :
    G.q x=groundParameter hm hn/H1.rep G.u x*
      leftGreen (fun y => m y*H1.rep G.u y) x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := ground_convolution G x
  rw [convolution_halves (density_rep_forcing_integrable hm G.u)] at h
  have hd := ground_convolution_slope G x
  rw [convolutionSlope] at hd
  rw [G.coordinate_eq]
  field_simp [(G.positive x).ne']
  linear_combination h-hd

end
end «2610.05164v2».HalfLine
