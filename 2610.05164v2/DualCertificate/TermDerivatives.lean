import «2610.05164v2».DualCertificate.PolynomialQuotients
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
Article: 2610.05164v2, Lemma 16.
Actual Frechet derivatives of the six polynomial-potential atoms.
Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` feeds
`«2610.05164v2».DualCertificate.PolynomialPotential.raw_b_factor` (raw b factor).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open «2610.05164v2».Residual Polynomial
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Defines `atom` of type `ℝ` by `match i with | 0 => Y.2.2.2 | 1 => Y.2.1 | 2 => Y.2.2.1 | 3 =>
Y.2.1^2 | 4 => Y.2.1*Y.2.2.1 | 5 => Y.2.2.1^2`.

Use: `«2610.05164v2».DualCertificate.atom_smooth` uses this definition to establish smoothness
to the stated order: `ContDiff ℝ ∞ (atom i)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def atom (i : Fin 6) (Y : State) : ℝ := match i with
  | 0 => Y.2.2.2
  | 1 => Y.2.1
  | 2 => Y.2.2.1
  | 3 => Y.2.1^2
  | 4 => Y.2.1*Y.2.2.1
  | 5 => Y.2.2.1^2

/--
Defines `atomDifferential` of type `ℝ` by `match i with | 0 => V.2.2.2 | 1 => V.2.1 | 2 =>
V.2.2.1 | 3 => 2*Y.2.1*V.2.1 | 4 => V.2.1*Y.2.2.1+Y.2.1*V.2.2.1 | 5 => 2*Y.2.2.1*V.2.2.1`.

Use: `«2610.05164v2».DualCertificate.atom_directional` rewrites with this definition to
establish the actual derivative at the stated point: `HasDerivAt (fun r : ℝ => atom i (Y+r •
V)) (atomDifferential i Y V) 0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def atomDifferential (i : Fin 6) (Y V : State) : ℝ := match i with
  | 0 => V.2.2.2
  | 1 => V.2.1
  | 2 => V.2.2.1
  | 3 => 2*Y.2.1*V.2.1
  | 4 => V.2.1*Y.2.2.1+Y.2.1*V.2.2.1
  | 5 => 2*Y.2.2.1*V.2.2.1

/--
Smoothness to the stated order: `ContDiff ℝ ∞ (atom i)`.

Use: `«2610.05164v2».DualCertificate.polynomialAtom_smooth` uses this assertion to establish
smoothness to the stated order: `ContDiff ℝ ∞ (polynomialAtom P i)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem atom_smooth (i : Fin 6) : ContDiff ℝ ∞ (atom i) := by fin_cases i <;> unfold atom <;> fun_prop

/--
The actual derivative at the stated point: `HasDerivAt (fun r : ℝ => atom i (Y+r • V))
(atomDifferential i Y V) 0`.

Use: `«2610.05164v2».DualCertificate.polynomialAtom_fderiv` uses this derivative formula to
establish the precise assertion is `fderiv ℝ (polynomialAtom P i) Y V= P.derivative.aeval
Y.1*V.1*atom i Y+P.aeval Y.1*atomDifferential i Y V`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem atom_directional (i : Fin 6) (Y V : State) :
    HasDerivAt (fun r : ℝ => atom i (Y+r • V)) (atomDifferential i Y V) 0 := by
  -- Check each member of the finite index type; no case is omitted.
  have h₀ : HasDerivAt (fun r : ℝ => Y.2.1+r*V.2.1) V.2.1 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const V.2.1).const_add Y.2.1
  have h₁ : HasDerivAt (fun r : ℝ => Y.2.2.1+r*V.2.2.1) V.2.2.1 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const V.2.2.1).const_add Y.2.2.1
  have hh : HasDerivAt (fun r : ℝ => Y.2.2.2+r*V.2.2.2) V.2.2.2 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const V.2.2.2).const_add Y.2.2.2
  fin_cases i
  · exact hh
  · exact h₀
  · exact h₁
  · convert! h₀.pow 2 using 1
    simp [atomDifferential]
  · convert! h₀.mul h₁ using 1
    simp [atomDifferential]
  · convert! h₁.pow 2 using 1
    simp [atomDifferential]

/--
Defines `polynomialAtom` of type `ℝ` by `P.aeval Y.1*atom i Y`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` uses this definition to
establish exact identity `fderiv ℝ P.raw Y V=∑ i : Fin 6, ((P.coefficient i).derivative.aeval
Y.1*V.1*atom i Y+ (P.coefficient i).aeval Y.1*atomDifferential i Y V)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def polynomialAtom (P : Polynomial ℚ) (i : Fin 6) (Y : State) : ℝ :=
  P.aeval Y.1*atom i Y

/--
Smoothness to the stated order: `ContDiff ℝ ∞ (polynomialAtom P i)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` rewrites with this
assertion to establish the identity `fderiv ℝ P.raw Y V=∑ i : Fin 6, ((P.coefficient
i).derivative.aeval Y.1*V.1*atom i Y+ (P.coefficient i).aeval Y.1*atomDifferential i Y V)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.atom_smooth` with the
arguments shown in the proof.
-/
theorem polynomialAtom_smooth (P : Polynomial ℚ) (i : Fin 6) :
    ContDiff ℝ ∞ (polynomialAtom P i) :=
  ((P.contDiff_aeval ∞).comp contDiff_fst).mul (atom_smooth i)

/--
The precise assertion is `fderiv ℝ (polynomialAtom P i) Y V= P.derivative.aeval Y.1*V.1*atom i
Y+P.aeval Y.1*atomDifferential i Y V`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` rewrites with this
identity to establish the identity `fderiv ℝ P.raw Y V=∑ i : Fin 6, ((P.coefficient
i).derivative.aeval Y.1*V.1*atom i Y+ (P.coefficient i).aeval Y.1*atomDifferential i Y V)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.atom_directional`,
`«2610.05164v2».DualCertificate.polynomialAtom_smooth` with the arguments shown in the proof.
-/
theorem polynomialAtom_fderiv (P : Polynomial ℚ) (i : Fin 6) (Y V : State) :
    fderiv ℝ (polynomialAtom P i) Y V=
      P.derivative.aeval Y.1*V.1*atom i Y+P.aeval Y.1*atomDifferential i Y V := by
  -- Use the identities/estimates `«2610.05164v2».DualCertificate.atom_directional`,
  -- `«2610.05164v2».DualCertificate.polynomialAtom_smooth` with the arguments shown in the
  -- proof.
  have hq : HasDerivAt (fun r : ℝ => Y.1+r*V.1) V.1 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const V.1).const_add Y.1
  have hp₀ : HasDerivAt (fun x : ℝ => P.aeval x) (P.derivative.aeval Y.1) (Y.1+0*V.1) := by
    simpa using P.hasDerivAt_aeval Y.1
  have hp := hp₀.comp (h := fun r : ℝ => Y.1+r*V.1) 0 hq
  have hd := hp.mul (atom_directional i Y V)
  have hy : HasDerivAt (fun r : ℝ => Y+r • V) V 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const V).const_add Y
  have hc := (polynomialAtom_smooth P i).differentiable (by norm_num) Y |>.hasFDerivAt
  have hc' : HasFDerivAt (polynomialAtom P i) (fderiv ℝ (polynomialAtom P i) Y) (Y+(0:ℝ) • V) := by
    simpa using hc
  have he := hc'.comp_hasDerivAt 0 hy
  apply he.unique
  convert! hd using 1
  simp

namespace PolynomialPotential
variable (P : PolynomialPotential)

/--
Defines `coefficient` of type `Polynomial ℚ` by `match i with | 0 => (C 2-X)^2*P.Ph | 1 => X*(C
2-X)^2*P.P₀ | 2 => X*(C 2-X)^2*P.P₁ | 3 => (C 2-X)^2*P.P₀₀ | 4 => (C 2-X)^2*P.P₀₁ | 5 => (C
2-X)^2*P.P₁₁`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.coefficient_right` uses this
definition to establish `(C 2-X)^2∣P.coefficient i`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def coefficient (i : Fin 6) : Polynomial ℚ := match i with
  | 0 => (C 2-X)^2*P.Ph
  | 1 => X*(C 2-X)^2*P.P₀
  | 2 => X*(C 2-X)^2*P.P₁
  | 3 => (C 2-X)^2*P.P₀₀
  | 4 => (C 2-X)^2*P.P₀₁
  | 5 => (C 2-X)^2*P.P₁₁

/--
Exact identity `P.raw Y=∑ i : Fin 6, polynomialAtom (P.coefficient i) i Y`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_fderiv` uses this identity to
establish exact identity `fderiv ℝ P.raw Y V=∑ i : Fin 6, ((P.coefficient i).derivative.aeval
Y.1*V.1*atom i Y+ (P.coefficient i).aeval Y.1*atomDifferential i Y V)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem raw_sum (Y : State) : P.raw Y=∑ i : Fin 6, polynomialAtom (P.coefficient i) i Y := by
  simp [Fin.sum_univ_succ,coefficient,polynomialAtom,atom,raw,inner]
  ring

/--
The precise assertion is `(C 2-X)^2∣P.coefficient i`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 16.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem coefficient_right (i : Fin 6) : (C 2-X)^2∣P.coefficient i := by
  fin_cases i <;> unfold coefficient
  · exact dvd_mul_right _ _
  · refine ⟨X*P.P₀,?_⟩; ring
  · refine ⟨X*P.P₁,?_⟩; ring
  · exact dvd_mul_right _ _
  · exact dvd_mul_right _ _
  · exact dvd_mul_right _ _

/--
The raw state gradient is the literal sum of the six atom gradients.

Exact identity `fderiv ℝ P.raw Y V=∑ i : Fin 6, ((P.coefficient i).derivative.aeval
Y.1*V.1*atom i Y+ (P.coefficient i).aeval Y.1*atomDifferential i Y V)`.

Use: `«2610.05164v2».DualCertificate.PolynomialPotential.raw_b_factor` rewrites with this
identity to establish the identity `bPotential κ P.raw (unnormalize κ
Z)=«2610.05164v2».Calibration.Q Z.1*P.flatB κ Z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem raw_fderiv (Y V : State) :
    fderiv ℝ P.raw Y V=∑ i : Fin 6,
      ((P.coefficient i).derivative.aeval Y.1*V.1*atom i Y+
        (P.coefficient i).aeval Y.1*atomDifferential i Y V) := by
  have he : P.raw=fun Y => ∑ i : Fin 6, polynomialAtom (P.coefficient i) i Y := funext P.raw_sum
  rw [he,fderiv_fun_sum (fun i _ => (polynomialAtom_smooth _ i).differentiable (by norm_num) Y)]
  simp only [sum_apply,polynomialAtom_fderiv]

end PolynomialPotential
end
end «2610.05164v2».DualCertificate
