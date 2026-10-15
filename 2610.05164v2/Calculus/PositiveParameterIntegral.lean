import «2610.05164v2».Calculus.CompactIntegral

/-!
Article: 2610.05164v2, Theorem 3.6.
Continuity of compact integrals for a positive real parameter.
Use: `«2610.05164v2».Calculus.positive_parameter_integral_continuous` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.S_continuous` (S continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => ∫ t in Icc a b,F κ t)`.

Use: `«2610.05164v2».DualCertificate.Data.cell_integral_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => ∫ t in Icc
((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ), 3*t^3*D.normalization.root κ t*(D.cells
side).affine i t)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem positive_parameter_integral_continuous {a b : ℝ} (F : Ioi (0:ℝ) → ℝ → ℝ)
    (hF : Continuous (fun p : Ioi (0:ℝ) × Icc a b => F p.1 p.2)) :
    Continuous (fun κ : Ioi (0:ℝ) => ∫ t in Icc a b,F κ t) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let G : ℝ → ℝ → ℝ := fun κ t => if hκ : 0<κ then F ⟨κ,hκ⟩ t else 0
  -- Establish continuity hG before using the function at limits or in calculus arguments.
  have hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Ioi (0:ℝ) ×ˢ Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    -- Establish continuity hm before using the function at limits or in calculus arguments.
    have hm : Continuous (fun p : Ioi (0:ℝ) ×ˢ Icc a b =>
        ((⟨p.val.1,p.property.1⟩ : Ioi (0:ℝ)),(⟨p.val.2,p.property.2⟩ : Icc a b))) := by
      exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    convert! hF.comp hm using 1
    funext p
    exact dite_eq_left p.property.1
  rw [continuous_iff_continuousAt]
  intro κ
  have hk : (0:ℝ)<κ := κ.property
  have hbox : Icc ((κ:ℝ)/2) (2*(κ:ℝ)) ×ˢ Icc a b ⊆ Ioi (0:ℝ) ×ˢ Icc a b := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by linarith [hk]) hp.1.1,hp.2⟩
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousAt (fun k : ℝ => ∫ t in Icc a b,G k t) κ :=
    (continuousOn_compact_integral (hG.mono hbox)).continuousAt
      (Icc_mem_nhds (by linarith [hk]) (by linarith [hk]))
  convert! hc.comp (continuous_subtype_val.continuousAt (x := κ)) using 1
  funext k
  have hkp : (0:ℝ)<k := k.property
  simp only [Function.comp_apply,G,dite_eq_left hkp]

end
end «2610.05164v2».Calculus
