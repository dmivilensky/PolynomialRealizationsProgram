import «2610.05164v2».Residual.CubicConjugate
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Article: 2610.05164v2, Theorem 3.6.
The C² assertion in Lemma 15, including the join at -3/2.
Use: `«2610.05164v2».Residual.psi_c2` feeds
`«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` (face Criterion continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Residual
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The actual derivative at the stated point: `HasDerivAt (fun x : ℝ => (max x 0)^n) ((n:ℝ)*(max x
0)^(n-1)) x`.

Use: `«2610.05164v2».Residual.positivePart_cube_c2` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 2 (fun x : ℝ => (max x 0)^3)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem positivePart_pow_derivative (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0)^n) ((n:ℝ)*(max x 0)^(n-1)) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h : (fun x : ℝ => (max x 0)^n) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [gt_mem_nhds hx] with t ht
      simp [max_eq_right ht.le,show n ≠ 0 by omega]
    simpa [max_eq_right hx.le,show n-1 ≠ 0 by omega] using
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq h
  · have hleft : HasDerivWithinAt (fun x : ℝ => (max x 0)^n) 0 (Iic 0) 0 := by
      apply (hasDerivWithinAt_const (0:ℝ) (Iic (0:ℝ)) (0:ℝ)).congr
      · intro t ht
        simp [max_eq_right (show t ≤ 0 from ht),show n ≠ 0 by omega]
      · simp [show n ≠ 0 by omega]
    have hright : HasDerivWithinAt (fun x : ℝ => (max x 0)^n) 0 (Ici 0) 0 := by
      have hp : HasDerivWithinAt (fun x : ℝ => x^n) 0 (Ici 0) 0 := by
        simpa [show n-1 ≠ 0 by omega] using (hasDerivAt_pow n (0:ℝ)).hasDerivWithinAt (s := Ici 0)
      apply hp.congr
      · intro t ht
        simp [max_eq_left (show 0 ≤ t from ht)]
      · simp
    have h := hleft.union hright
    simpa [Iic_union_Ici,show n-1 ≠ 0 by omega] using h
  · have h : (fun x : ℝ => (max x 0)^n) =ᶠ[𝓝 x] fun x => x^n := by
      filter_upwards [lt_mem_nhds hx] with t ht
      rw [max_eq_left ht.le]
    simpa [max_eq_left hx.le] using ((hasDerivAt_id x).pow n).congr_of_eventuallyEq h

/--
Smoothness to the stated order: `ContDiff ℝ 1 (fun x : ℝ => (max x 0)^2)`.

Use: `«2610.05164v2».Residual.positivePart_cube_c2` uses this identity to establish smoothness
to the stated order: `ContDiff ℝ 2 (fun x : ℝ => (max x 0)^3)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem positivePart_square_c1 : ContDiff ℝ 1 (fun x : ℝ => (max x 0)^2) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [contDiff_one_iff_deriv]
  have hd := positivePart_pow_derivative 2 (by omega)
  refine ⟨fun x => (hd x).differentiableAt,?_⟩
  have he : deriv (fun x : ℝ => (max x 0)^2)=fun x => 2*max x 0 := by
    funext x
    simpa using (hd x).deriv
  rw [he]
  fun_prop

/--
Smoothness to the stated order: `ContDiff ℝ 2 (fun x : ℝ => (max x 0)^3)`.

Use: `«2610.05164v2».Residual.psi_c2` uses this identity to establish smoothness to the stated
order: `ContDiff ℝ 2 psi`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem positivePart_cube_c2 : ContDiff ℝ 2 (fun x : ℝ => (max x 0)^3) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [show (2 : WithTop ℕ∞)=1+1 by norm_num,contDiff_succ_iff_deriv]
  have hd := positivePart_pow_derivative 3 (by omega)
  refine ⟨fun x => (hd x).differentiableAt,by simp,?_⟩
  have he : deriv (fun x : ℝ => (max x 0)^3)=fun x => 3*(max x 0)^2 := by
    funext x
    simpa using (hd x).deriv
  rw [he]
  exact contDiff_const.mul positivePart_square_c1

/--
Smoothness to the stated order: `ContDiff ℝ 2 psi`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this assertion to
establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.positivePart_cube_c2` with the
arguments shown in the proof.
-/
theorem psi_c2 : ContDiff ℝ 2 psi := by
  unfold psi
  exact ((contDiff_id.neg.sub contDiff_const).add
    (contDiff_const.mul (positivePart_cube_c2.comp (contDiff_id.add contDiff_const))))

/--
The actual derivative at the stated point: `HasDerivAt psi (-1+4/9*(max (x+3/2) 0)^2) x`.

Use: `«2610.05164v2».Residual.psi_second_derivative` uses this derivative formula to establish
the actual derivative at the stated point: `HasDerivAt (deriv psi) (8/9*max (x+3/2) 0) x`.

Article: 2610.05164v2, Theorem 3.6.

Proof: Use the identities/estimates `«2610.05164v2».Residual.positivePart_pow_derivative` with
the arguments shown in the proof.
-/
theorem psi_derivative (x : ℝ) : HasDerivAt psi (-1+4/9*(max (x+3/2) 0)^2) x := by
  have hp := (positivePart_pow_derivative 3 (by omega) (x+3/2)).comp x
    ((hasDerivAt_id x).add_const (3/2:ℝ))
  have h := (((hasDerivAt_id x).neg.sub_const (1/2:ℝ)).add (hp.const_mul (4/27:ℝ)))
  change HasDerivAt psi (-1+4/27*((3:ℝ)*(max (x+3/2) 0)^2*1)) x at h
  convert h using 1
  ring

/--
The actual derivative at the stated point: `HasDerivAt (deriv psi) (8/9*max (x+3/2) 0) x`.

Use: `«2610.05164v2».Numerics.StateJetOn.psi` uses this derivative formula in the displayed
construction of `psi`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem psi_second_derivative (x : ℝ) :
    HasDerivAt (deriv psi) (8/9*max (x+3/2) 0) x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : deriv psi=fun x => -1+4/9*(max (x+3/2) 0)^2 :=
    funext (fun x => (psi_derivative x).deriv)
  rw [he]
  have hp := (positivePart_pow_derivative 2 (by omega) (x+3/2)).comp x
    ((hasDerivAt_id x).add_const (3/2:ℝ))
  have h := (hasDerivAt_const x (-1:ℝ)).add (hp.const_mul (4/9:ℝ))
  change HasDerivAt (fun x => -1+4/9*(max (x+3/2) 0)^2)
    (0+4/9*((2:ℝ)*(max (x+3/2) 0)^1*1)) x at h
  convert h using 1
  ring

end
end «2610.05164v2».Residual
