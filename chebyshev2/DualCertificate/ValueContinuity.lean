import chebyshev2.DualCertificate.PriceCost
import chebyshev2.DualCertificate.CertificateAssembly
import chebyshev2.DualCertificate.ObservationContinuity
import chebyshev2.DualCertificate.MassContinuity
import chebyshev2.Calibration.BaseContinuity

/-!
Article: chebyshev2, Theorem 3.6.
Continuity of the actual certificate price cost and value.
Use: `chebyshev2.DualCertificate.Data.value_continuous` feeds
`chebyshev2.DualCertificate.Data.packed_value_tendsto` (packed value tendsto).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace chebyshev2.DualCertificate.Data
noncomputable section
open Set Real MeasureTheory chebyshev2.Calculus chebyshev2.Residual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (D : chebyshev2.DualCertificate.Data)

/--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => ∫ t in Icc ((D.cells
side).lo i:ℝ) ((D.cells side).hi i:ℝ), 3*t^3*D.normalization.root κ t*(D.cells side).affine i
t)`.

Use: `chebyshev2.DualCertificate.Data.priceCost_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => priceCost κ
(D.τ:ℝ) (D.price κ.property).value)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`chebyshev2.Calculus.positive_parameter_integral_continuous`,
`chebyshev2.DualCertificate.NormalizedCalibration.root_smooth`,
`chebyshev2.DualCertificate.Cells.cell_inside` with the arguments shown in the proof.
-/
theorem cell_integral_continuous (side : Side) (i : Fin (D.cells side).count) :
    Continuous (fun κ : Ioi (0:ℝ) => ∫ t in Icc ((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ),
      3*t^3*D.normalization.root κ t*(D.cells side).affine i t) := by
  -- Use the identities/estimates
  -- `chebyshev2.Calculus.positive_parameter_integral_continuous`,
  -- `chebyshev2.DualCertificate.NormalizedCalibration.root_smooth`,
  -- `chebyshev2.DualCertificate.Cells.cell_inside` with the arguments shown in the proof.
  apply positive_parameter_integral_continuous
  -- Establish continuity hm before using the function at limits or in calculus arguments.
  have hm : Continuous (fun p : Ioi (0:ℝ) × Icc ((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ) =>
      ((p.1:ℝ),(p.2:ℝ))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hr := D.normalization.root_smooth.continuousOn.comp_continuous hm
    (fun p => ⟨p.1.property,(D.cells side).cell_inside i p.2.property⟩)
  -- Establish continuity ht before using the function at limits or in calculus arguments.
  have ht : Continuous (fun p : Ioi (0:ℝ) × Icc ((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ) => (p.2:ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.mul (ht.pow 3)).mul hr).mul (by unfold Cells.affine;fun_prop)

 /--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => priceCost κ (D.τ:ℝ)
(D.price κ.property).value)`.

Use: `chebyshev2.DualCertificate.Data.value_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun p : ObservationDomain =>
D.analytic.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem priceCost_continuous :
    Continuous (fun κ : Ioi (0:ℝ) => priceCost κ (D.τ:ℝ) (D.price κ.property).value) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun κ : Ioi (0:ℝ) => priceCost κ (D.τ:ℝ) (D.price κ.property).value)=
      fun κ : Ioi (0:ℝ) => ((∑ i,∫ t in Icc ((D.cells Side.left).lo i:ℝ) ((D.cells Side.left).hi i:ℝ),
        3*t^3*D.normalization.root κ t*(D.cells Side.left).affine i t)+
       (∑ i,∫ t in Icc ((D.cells Side.right).lo i:ℝ) ((D.cells Side.right).hi i:ℝ),
        3*t^3*D.normalization.root κ t*(D.cells Side.right).affine i t))/(κ:ℝ)+
      (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity κ.property x) := funext (fun κ : Ioi (0:ℝ) => D.price_cost_cells κ.property)
  rw [he]
  exact (((continuous_finsetSum _ (fun i _ => D.cell_integral_continuous Side.left i)).add
    (continuous_finsetSum _ (fun i _ => D.cell_integral_continuous Side.right i))).div
      continuous_subtype_val (fun κ => κ.property.ne')).add
        (continuous_const.mul (continuous_const.sub D.calibration.comparisonMass_continuous))

 /--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => D.analytic.comparisonH
κ.property s)`.

Use: `chebyshev2.DualCertificate.Data.value_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun p : ObservationDomain =>
D.analytic.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonH_continuous {s : ℝ} (hs : 0≤s) :
    Continuous (fun κ : Ioi (0:ℝ) => D.analytic.comparisonH κ.property s) := by
  convert! D.normalization.H_continuous hs using 1
  funext κ
  exact (D.normalization.H_actual (fun _ hq => D.Gamma_symmetric hq) κ.property hs).symm

 /--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => D.analytic.comparisonS
κ.property)`.

Use: `chebyshev2.DualCertificate.Data.value_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun p : ObservationDomain =>
D.analytic.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem comparisonS_continuous :
    Continuous (fun κ : Ioi (0:ℝ) => D.analytic.comparisonS κ.property) := by
  convert! D.normalization.S_continuous using 1
  funext κ
  exact (D.normalization.S_actual (fun _ hq => D.Gamma_symmetric hq) κ.property).symm

/--
Defines `ObservationDomain` of type `` by `Ioi (0:ℝ) × ℝ × ℝ × ℝ × ℝ`.

Use: `chebyshev2.DualCertificate.Data.value_continuous` uses this definition to establish
continuity of the displayed function: `Continuous (fun p : ObservationDomain =>
D.analytic.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.
-/
abbrev ObservationDomain := Ioi (0:ℝ) × ℝ × ℝ × ℝ × ℝ

/--
Continuity of the displayed function: `Continuous (fun p : ObservationDomain =>
D.analytic.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)`.

Use: `chebyshev2.DualCertificate.Data.packed_value_tendsto` uses this continuity result to
establish the limit stated in that declaration.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.base_continuousOn`,
`chebyshev2.DualCertificate.Data.comparisonH_continuous`,
`chebyshev2.DualCertificate.Data.comparisonS_continuous` with the arguments shown in the
proof.
-/
theorem value_continuous : Continuous (fun p : ObservationDomain =>
    D.analytic.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  -- Establish continuity hbase before using the function at limits or in calculus arguments.
  have hbase : Continuous (fun p : ObservationDomain => D.calibration.base p.1 p.2.2.2.1) :=
    D.calibration.base_continuousOn.comp_continuous
      (f := fun p : ObservationDomain => ((p.1:ℝ),p.2.2.2.1)) (by fun_prop) (fun p => p.1.property)
  -- Establish continuity hH₀ before using the function at limits or in calculus arguments.
  have hH₀ := (D.comparisonH_continuous (by norm_num : (0:ℝ)≤32)).comp (continuous_fst : Continuous (fun p : ObservationDomain => p.1))
  -- Establish continuity hH₁ before using the function at limits or in calculus arguments.
  have hH₁ := (D.comparisonH_continuous (by norm_num : (0:ℝ)≤64)).comp (continuous_fst : Continuous (fun p : ObservationDomain => p.1))
  -- Establish continuity hS before using the function at limits or in calculus arguments.
  have hS := D.comparisonS_continuous.comp (continuous_fst : Continuous (fun p : ObservationDomain => p.1))
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc := D.priceCost_continuous.comp (continuous_fst : Continuous (fun p : ObservationDomain => p.1))
  exact (((hbase.add (continuous_const.mul (continuous_snd.fst.sub hH₀))).add
    (continuous_const.mul (continuous_snd.snd.fst.sub hH₁))).add
    (continuous_const.mul (continuous_snd.snd.snd.snd.sub hS))).sub hc

end
end chebyshev2.DualCertificate.Data
