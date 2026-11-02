import jacobi.Trichotomy.PhysicalEndpointLimits
import jacobi.Trichotomy.PackingCoordinate
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
Article: jacobi, Proposition C.4.
The actual positive subcritical profile has exponent 2*gamma<1.
Its reciprocal is therefore genuinely integrable from zero to the
physical midpoint. The proof separates a power-controlled original
endpoint neighborhood from the continuous remaining compact segment.
Use: subcritical_coordinate_endpoint constructs the actual finite packing radius and its endpoint primitive, without assuming a compact support or an integrability certificate.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The original reciprocal persymmetric profile is genuinely integrable up to the physical endpoint throughout the subcritical order range.
Use: subcritical_coordinate_endpoint constructs the actual finite packing radius and its endpoint primitive, without assuming a compact support or an integrability certificate.
Article: jacobi, Proposition C.4.
Proof: the proved positive profile ratio is eventually at least c_alpha/2, so its actual reciprocal is bounded by (2/c_alpha)*t^(-2*gamma). This power is integrable because 2*gamma<1. Away from zero, actual profile positivity and continuity give ordinary compact-segment integrability. -/
theorem subcritical_reciprocal_integrable {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    IntervalIntegrable (fun t : ℝ => 1/physicalProfile a ha t) volume 0 (1/2) := by
  -- The finite interval near zero is chosen from the genuine positive spectral endpoint constant.
  have hc := endpointConstant_pos a ha hs
  have hg : 2*gamma a<1 := by dsimp only [gamma]; linarith
  have hnear : {t : ℝ | endpointConstant a ha/2<physicalProfile a ha t/t^(2*gamma a)}∈𝓝[>] (0:ℝ) :=
    (physicalProfile_subcritical_limit ha hs).eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨d,hd,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let e := min (d/2) (1/4)
  have he : 0<e := lt_min (half_pos hd) (by norm_num)
  have hed : e<d := (min_le_left (d/2) (1/4)).trans_lt (by linarith [show 0<d from hd])
  have hehalf : e<1/2 := (min_le_right (d/2) (1/4)).trans_lt (by norm_num)
  have hm : AEStronglyMeasurable (fun t : ℝ => 1/physicalProfile a ha t) volume :=
    (measurable_const.div (physicalProfile_continuous a ha).measurable).aestronglyMeasurable
  have hp : IntegrableOn (fun t : ℝ => (2/endpointConstant a ha)*t^(-2*gamma a)) (Ioc 0 e) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le he.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (show -1 < -2*gamma a by linarith))).const_mul _
  have hi : IntervalIntegrable (fun t : ℝ => 1/physicalProfile a ha t) volume 0 e := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le he.le]
    apply hp.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htp : t∈Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.trans_lt (hehalf.trans (by norm_num))⟩
    have hphi := physicalProfile_pos a ha htp
    have hpower := Real.rpow_pos_of_pos ht.1 (2*gamma a)
    have hb := (lt_div_iff₀ hpower).mp (hbound ⟨ht.1,ht.2.trans_lt hed⟩)
    rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hphi)]
    have hrec := one_div_le_one_div_of_le (mul_pos (half_pos hc) hpower) hb.le
    apply hrec.trans_eq
    rw [show -2*gamma a= -(2*gamma a) by ring,Real.rpow_neg ht.1.le]
    field_simp [hc.ne',hpower.ne']
  have hseg : uIcc e (1/2:ℝ)⊆Ioo (0:ℝ) 1 :=
    (ordConnected_Ioo : OrdConnected (Ioo (0:ℝ) 1)).uIcc_subset
      ⟨he,hehalf.trans (by norm_num)⟩ (by constructor <;> norm_num)
  exact hi.trans (((physicalProfile_reciprocal_continuousOn a ha).mono hseg).intervalIntegrable)

end
end jacobi.Trichotomy
