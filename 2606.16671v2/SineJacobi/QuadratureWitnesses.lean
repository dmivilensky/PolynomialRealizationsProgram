import «2606.16671v2».SineJacobi.EnergyWitnesses
import «2606.16671v2».SineJacobi.EnergyQuadrature

/-!
Article: 2606.16671v2, Theorem 5.2.
Panel values never evaluate validity checks.
Use: `«2606.16671v2».SineJacobi.panelWitnessValue_correct` feeds
`«2606.16671v2».SineJacobi.panelCertificateCheck_correct` (Accepted panel certificates bound the
actual composite quadrature).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
open LeanCert.Core «2606.16671v2».Numerics

/--
Energy witnesses at the left endpoint, midpoint and right endpoint of one graded quadrature
panel.

Use: `«2606.16671v2».SineJacobi.panelWitnessValid` uses this record of data and proof
obligations in the displayed construction of `panelWitnessValid`. Its inputs and component
formulas are fixed by that definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
structure PanelWitness where
  /-- Energy witness at the panel left endpoint. -/
  left : EnergyWitness
  /-- Energy witness at the panel midpoint. -/
  middle : EnergyWitness
  /-- Energy witness at the panel right endpoint. -/
  right : EnergyWitness

/--
Supplies the typeclass `Lean.ToExpr PanelWitness` by the displayed field definitions/proofs.
Each proof field establishes the corresponding class law.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2606.16671v2, Theorem 5.2.
-/
instance : Lean.ToExpr PanelWitness where
  toTypeExpr := Lean.mkConst ``PanelWitness
  toExpr w := Lean.mkApp3 (Lean.mkConst ``PanelWitness.mk)
    (Lean.toExpr w.left) (Lean.toExpr w.middle) (Lean.toExpr w.right)

/--
Defines `gradedWitnessValue` of type `IntervalRat` by `if h : 0 ≤ s ∧ s ≤ 1/128 then ⟨0,
12*s^5, mul_nonneg (by norm_num) (pow_nonneg h.1 _)⟩ else rounded (IntervalRat.scale (3*s^2)
(energyWitnessValue ws))`.

Use:
`_private.«2606.16671v2».SineJacobi.QuadratureWitnesses.0.«2606.16671v2».SineJacobi.gradedWitnessValue_correct`
uses this definition to establish membership in the specified domain/enclosure: `gradedEnergy s
∈ gradedWitnessValue s ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
private def gradedWitnessValue (s : ℚ) (ws : EnergyWitness) : IntervalRat :=
  if h : 0 ≤ s ∧ s ≤ 1/128 then ⟨0, 12*s^5, mul_nonneg (by norm_num) (pow_nonneg h.1 _)⟩
  else rounded (IntervalRat.scale (3*s^2) (energyWitnessValue ws))

/--
Defines `gradedWitnessValid` of type `Bool` by `if 0 ≤ s ∧ s ≤ 1/128 then true else
energyWitnessValid (s^3/2) ws`.

Use:
`_private.«2606.16671v2».SineJacobi.QuadratureWitnesses.0.«2606.16671v2».SineJacobi.gradedWitnessValue_correct`
uses this definition to establish membership in the specified domain/enclosure: `gradedEnergy s
∈ gradedWitnessValue s ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
private def gradedWitnessValid (s : ℚ) (ws : EnergyWitness) : Bool :=
  if 0 ≤ s ∧ s ≤ 1/128 then true else energyWitnessValid (s^3/2) ws

/--
Membership in the specified domain/enclosure: `gradedEnergy s ∈ gradedWitnessValue s ws`.

Use: `«2606.16671v2».SineJacobi.panelWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∈
panelWitnessValue N j ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.gradedEnergy_bound`,
`«2606.16671v2».SineJacobi.energyWitnessValue_correct`, `«2606.16671v2».Numerics.mem_rounded`
with the arguments shown in the proof.
-/
private theorem gradedWitnessValue_correct {ws : EnergyWitness} {s : ℚ} (hs : 0 < s) (hs1 : s ≤ 1)
    (h : gradedWitnessValid s ws = true) : gradedEnergy s ∈ gradedWitnessValue s ws := by
  -- Apply
  -- `_private.«2606.16671v2».SineJacobi.QuadratureWitnesses.0.«2606.16671v2».SineJacobi.gradedWitnessValid`,
  -- `_private.«2606.16671v2».SineJacobi.QuadratureWitnesses.0.«2606.16671v2».SineJacobi.gradedWitnessValue`,
  -- `«2606.16671v2».SineJacobi.gradedEnergy` to the displayed hypotheses, then match the
  -- resulting expression to the goal.
  unfold gradedWitnessValue gradedWitnessValid at *
  split_ifs at * with hsmall
  · have hs' : (0:ℝ) < s := by exact_mod_cast hs
    have hs1' : (s:ℝ) ≤ 1 := by exact_mod_cast hs1
    simpa only [IntervalRat.mem_def, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_zero] using
      gradedEnergy_bound hs' hs1'
  · have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
    have hs1' : (s:ℝ) ≤ 1 := by exact_mod_cast hs1
    have ht : ((s^3/2:ℚ):ℝ) ∈ Set.Ioo 0 1 := by
      push_cast
      refine ⟨by positivity, ?_⟩
      have hh := pow_le_pow_left₀ hs'.le hs1' 3
      norm_num at hh
      linarith
    have hb := energyWitnessValue_correct ht h
    convert mem_rounded (IntervalRat.mem_scale (3*s^2) hb) using 1;
      simp only [gradedEnergy, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]

/--
Panel values never evaluate validity checks.

Use: `«2606.16671v2».SineJacobi.panelWitnessValue_correct` uses this definition to establish
membership in the specified domain/enclosure: `simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∈
panelWitnessValue N j ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def panelWitnessValue (N j : ℕ) (ws : PanelWitness) : IntervalRat :=
  let A := gradedWitnessValue ((j:ℚ)/N) ws.left
  let B := gradedWitnessValue ((2*j+1:ℚ)/(2*N)) ws.middle
  let C := gradedWitnessValue ((j+1:ℚ)/N) ws.right
  rounded (IntervalRat.scale (1/(6*N))
    (IntervalRat.add (IntervalRat.add A (IntervalRat.scale 4 B)) C))

/--
Defines `panelWitnessValid` of type `Bool` by `gradedWitnessValid ((j:ℚ)/N) ws.left &&
gradedWitnessValid ((2*j+1:ℚ)/(2*N)) ws.middle && gradedWitnessValid ((j+1:ℚ)/N) ws.right`.

Use: `«2606.16671v2».SineJacobi.panelWitnessValue_correct` rewrites with this definition to
establish membership in the specified domain/enclosure: `simpson gradedEnergy ((j:ℝ)/N)
((j+1:ℝ)/N) ∈ panelWitnessValue N j ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def panelWitnessValid (N j : ℕ) (ws : PanelWitness) : Bool :=
  gradedWitnessValid ((j:ℚ)/N) ws.left &&
    gradedWitnessValid ((2*j+1:ℚ)/(2*N)) ws.middle &&
    gradedWitnessValid ((j+1:ℚ)/N) ws.right

noncomputable section
open «2606.16671v2».Analysis
set_option backward.isDefEq.respectTransparency false

/--
Membership in the specified domain/enclosure: `simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∈
panelWitnessValue N j ws`.

Use:
`_private.«2606.16671v2».SineJacobi.PanelCertificates.0.«2606.16671v2».SineJacobi.panelAccepted_bounds`
uses this assertion to prove the bound `(min c.bounds.1
c.bounds.2:ℝ)/2^64 ≤ simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∧ simpson gradedEnergy
((j:ℝ)/N) ((j+1:ℝ)/N) ≤ (max c.bounds.1 c.bounds.2:ℝ)/2^64`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem panelWitnessValue_correct {ws : PanelWitness} {N j : ℕ} (hj : 1 ≤ j) (hjN : j < N)
    (h : panelWitnessValid N j ws = true) : simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) ∈ panelWitnessValue N j ws := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hN : 0 < (N:ℚ) := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 < (j:ℚ)/N ∧ (j:ℚ)/N ≤ 1 := by
    constructor
    · exact div_pos (by exact_mod_cast (show 0 < j by omega)) hN
    · exact (div_le_one hN).mpr (by exact_mod_cast hjN.le)
  have hb : 0 < (2*j+1:ℚ)/(2*N) ∧ (2*j+1:ℚ)/(2*N) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast (show 2*j+1 ≤ 2*N by omega)
  have hc : 0 < (j+1:ℚ)/N ∧ (j+1:ℚ)/N ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one hN).mpr
      exact_mod_cast (show j+1 ≤ N by omega)
  simp only [panelWitnessValid, Bool.and_eq_true] at h
  have hval := mem_rounded (IntervalRat.mem_scale (1/(6*N)) (IntervalRat.mem_add
    (IntervalRat.mem_add (gradedWitnessValue_correct ha.1 ha.2 h.1.1)
      (IntervalRat.mem_scale 4 (gradedWitnessValue_correct hb.1 hb.2 h.1.2)))
    (gradedWitnessValue_correct hc.1 hc.2 h.2)))
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast at hval
  have hmid : (2*(j:ℝ)+1)/(2*N) = (((j:ℝ)/N)+((j+1:ℝ)/N))/2 := by
    field_simp; ring
  rw [hmid] at hval
  have he : simpson gradedEnergy ((j:ℝ)/N) ((j+1:ℝ)/N) =
      (1/(6*N))*(gradedEnergy ((j:ℝ)/N)+
        4*gradedEnergy ((((j:ℝ)/N)+((j+1:ℝ)/N))/2)+gradedEnergy ((j+1:ℝ)/N)) := by
    unfold simpson
    field_simp
    ring
  rw [he]
  simpa only [panelWitnessValue] using hval

end
end «2606.16671v2».SineJacobi
