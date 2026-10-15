import «2606.16671v2».SineJacobi.EnergyFormula
import «2606.16671v2».SineJacobi.EllipticWitnesses
import «2606.16671v2».Numerics.Cosine

/-!
Article: 2606.16671v2, Theorem 5.2.
A checked enclosure of the actual energy density at a rational interior point.
Use: `«2606.16671v2».SineJacobi.energyWitnessValue_correct` feeds
`«2606.16671v2».SineJacobi.panelWitnessValue_correct` (panel Witness Value correct).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
open Real Set LeanCert.Core «2606.16671v2».Numerics

/--
Defines `witnessPi` of type `IntervalRat` by `⟨314159265358979323846/10^20,
314159265358979323847/10^20, by norm_num⟩`.

Use:
`_private.«2606.16671v2».SineJacobi.EnergyWitnesses.0.«2606.16671v2».SineJacobi.witnessPi_mem`
uses this definition to establish membership in the specified domain/enclosure: `Real.pi ∈
witnessPi`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
private def witnessPi : IntervalRat :=
  ⟨314159265358979323846/10^20, 314159265358979323847/10^20, by norm_num⟩

/--
Membership in the specified domain/enclosure: `Real.pi ∈ witnessPi`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValue_correct` uses this assertion to establish
membership in the specified domain/enclosure: `energyDensity t ∈ energyWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem witnessPi_mem : Real.pi ∈ witnessPi := by
  have hl := Real.pi_gt_d20.le
  have hu := Real.pi_lt_d20.le
  norm_num [witnessPi, IntervalRat.mem_def] at hl hu ⊢
  exact ⟨hl, hu⟩

/--
A checked enclosure of the actual energy density at a rational interior point.

Use: `«2606.16671v2».SineJacobi.energyWitnessValid` uses this record of data and proof
obligations in the displayed construction of `energyWitnessValid`. Its inputs and component
formulas are fixed by that definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
structure EnergyWitness where
  /-- Cosine enclosure needed to obtain the complementary elliptic moduli. -/
  cosine : CosineWitness
  /-- Finite Landen-descent witness list for the first elliptic factor. -/
  left : List EllipticWitness
  /-- Finite Landen-descent witness list for the complementary elliptic factor. -/
  right : List EllipticWitness

/--
Supplies the typeclass `Lean.ToExpr EnergyWitness` by the displayed field definitions/proofs.
Each proof field establishes the corresponding class law.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2606.16671v2, Theorem 5.2.
-/
instance : Lean.ToExpr EnergyWitness where
  toTypeExpr := Lean.mkConst ``EnergyWitness
  toExpr w := Lean.mkApp3 (Lean.mkConst ``EnergyWitness.mk)
    (Lean.toExpr w.cosine) (Lean.toExpr w.left) (Lean.toExpr w.right)

/--
Defines `energyArgument` of type `IntervalRat` by `IntervalRat.scale t witnessPi`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValid` uses this definition in the displayed
construction of `energyWitnessValid`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def energyArgument (t : ℚ) : IntervalRat := IntervalRat.scale t witnessPi

/--
Defines `energyModuli` of type `IntervalRat × IntervalRat` by `let C := cosineWitnessValue w
let X := rounded (IntervalRat.scale (1/2) (IntervalRat.sub (IntervalRat.singleton 1) C)) let Y
:= rounded (IntervalRat.scale (1/2) (IntervalRat.add (IntervalRat.singleton 1) C)) (X,Y)`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValid` uses this definition in the displayed
construction of `energyWitnessValid`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def energyModuli (w : CosineWitness) : IntervalRat × IntervalRat :=
  let C := cosineWitnessValue w
  let X := rounded (IntervalRat.scale (1/2) (IntervalRat.sub (IntervalRat.singleton 1) C))
  let Y := rounded (IntervalRat.scale (1/2) (IntervalRat.add (IntervalRat.singleton 1) C))
  (X,Y)

/--
Defines `energyWitnessValue` of type `IntervalRat` by `let X := (energyModuli ws.cosine).1 let
Y := (energyModuli ws.cosine).2 let A := ellipticWitnessValue ws.left let B :=
ellipticWitnessValue ws.right rounded (IntervalRat.scale 4 (IntervalRat.mul (IntervalRat.mul X
Y) (IntervalRat.mul (IntervalRat.pow A 2) (IntervalRat.pow B 2))))`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValue_correct` uses this definition to establish
membership in the specified domain/enclosure: `energyDensity t ∈ energyWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def energyWitnessValue (ws : EnergyWitness) : IntervalRat :=
  let X := (energyModuli ws.cosine).1
  let Y := (energyModuli ws.cosine).2
  let A := ellipticWitnessValue ws.left
  let B := ellipticWitnessValue ws.right
  rounded (IntervalRat.scale 4 (IntervalRat.mul (IntervalRat.mul X Y)
    (IntervalRat.mul (IntervalRat.pow A 2) (IntervalRat.pow B 2))))

/--
Defines `energyWitnessValid` of type `Bool` by `cosineWitnessValid (energyArgument t) ws.cosine
&& ellipticWitnessValid ws.left (energyModuli ws.cosine).1 && ellipticWitnessValid ws.right
(energyModuli ws.cosine).2`.

Use: `«2606.16671v2».SineJacobi.energyWitnessValue_correct` rewrites with this definition to
establish membership in the specified domain/enclosure: `energyDensity t ∈ energyWitnessValue
ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def energyWitnessValid (t : ℚ) (ws : EnergyWitness) : Bool :=
  cosineWitnessValid (energyArgument t) ws.cosine &&
    ellipticWitnessValid ws.left (energyModuli ws.cosine).1 &&
    ellipticWitnessValid ws.right (energyModuli ws.cosine).2

noncomputable section

/--
Membership in the specified domain/enclosure: `energyDensity t ∈ energyWitnessValue ws`.

Use:
`_private.«2606.16671v2».SineJacobi.QuadratureWitnesses.0.«2606.16671v2».SineJacobi.gradedWitnessValue_correct`
uses this assertion to establish membership in the specified domain/enclosure: `gradedEnergy s
∈ gradedWitnessValue s ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».Numerics.cosineWitnessValue_correct`,
`_private.«2606.16671v2».SineJacobi.EnergyWitnesses.0.«2606.16671v2».SineJacobi.witnessPi_mem`,
`«2606.16671v2».Numerics.mem_rounded` with the arguments shown in the proof.
-/
theorem energyWitnessValue_correct {ws : EnergyWitness} {t : ℚ} (ht : (t:ℝ) ∈ Set.Ioo 0 1)
    (h : energyWitnessValid t ws = true) : energyDensity t ∈ energyWitnessValue ws := by
  -- Use the identities/estimates `«2606.16671v2».Numerics.cosineWitnessValue_correct`,
  -- `_private.«2606.16671v2».SineJacobi.EnergyWitnesses.0.«2606.16671v2».SineJacobi.witnessPi_mem`,
  -- `«2606.16671v2».Numerics.mem_rounded` with the arguments shown in the proof.
  simp only [energyWitnessValid, Bool.and_eq_true] at h
  let C := cosineWitnessValue ws.cosine
  let X := rounded (IntervalRat.scale (1/2) (IntervalRat.sub (IntervalRat.singleton 1) C))
  let Y := rounded (IntervalRat.scale (1/2) (IntervalRat.add (IntervalRat.singleton 1) C))
  have hc := cosineWitnessValue_correct (IntervalRat.mem_scale t witnessPi_mem) h.1.1
  have ho : (1:ℝ) ∈ IntervalRat.singleton 1 := by simpa using IntervalRat.mem_singleton 1
  have hx := mem_rounded (IntervalRat.mem_scale (1/2) (IntervalRat.mem_sub ho hc))
  have hy := mem_rounded (IntervalRat.mem_scale (1/2) (IntervalRat.mem_add ho hc))
  have hx' : (1-Real.cos (Real.pi*t))/2 ∈ X := by
    convert hx using 1; push_cast; ring_nf
  have hy' : (1+Real.cos (Real.pi*t))/2 ∈ Y := by
    convert hy using 1; push_cast; ring_nf
  have hcos : -1 < Real.cos (Real.pi*t) ∧ Real.cos (Real.pi*t) < 1 := by
    have hs := Real.sin_pos_of_mem_Ioo
      (show Real.pi*t ∈ Set.Ioo (0:ℝ) Real.pi from
        ⟨mul_pos Real.pi_pos ht.1, by nlinarith [Real.pi_pos, ht.2]⟩)
    have hh := Real.sin_sq_add_cos_sq (Real.pi*t)
    constructor <;> nlinarith [sq_pos_of_pos hs]
  have hA := ellipticWitnessValue_correct hx' (show (1-Real.cos (Real.pi*t))/2 ∈ Set.Ico (0:ℝ) 1 by
    constructor <;> linarith [hcos.1, hcos.2]) h.1.2
  have hB := ellipticWitnessValue_correct hy' (show (1+Real.cos (Real.pi*t))/2 ∈ Set.Ico (0:ℝ) 1 by
    constructor <;> linarith [hcos.1, hcos.2]) h.2
  change energyDensity t ∈ rounded (IntervalRat.scale 4 (IntervalRat.mul (IntervalRat.mul X Y)
    (IntervalRat.mul (IntervalRat.pow (ellipticWitnessValue ws.left) 2)
      (IntervalRat.pow (ellipticWitnessValue ws.right) 2))))
  rw [energyDensity_ellipticA ht]
  convert mem_rounded (IntervalRat.mem_scale 4 (IntervalRat.mem_mul
    (IntervalRat.mem_mul hx' hy') (IntervalRat.mem_mul
      (IntervalRat.mem_pow hA 2) (IntervalRat.mem_pow hB 2)))) using 1; push_cast; ring

end
end «2606.16671v2».SineJacobi
