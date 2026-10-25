import polyak.Boundary.P1.Continuation
import polyak.Boundary.P1.Geometry
import polyak.Boundary.P1.Physical
import polyak.Boundary.P1.SpiralStrict
import polyak.Boundary.P1.LocalExpansion

/-!
Article: Proposition p1physical on the complete closed physical P1 arc.
Every box reserve, finite lag, infinite tail, exact endpoint, and source root is discharged.
-/
noncomputable section
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric Filter
open scoped Topology

theorem prefixEnd_pos : 0<polyak.Certificates.Continuation.P1.Geometry.prefixEnd := by
  norm_num [polyak.Certificates.Continuation.P1.Geometry.prefixEnd]

theorem prefixEnd_lt_zW : polyak.Certificates.Continuation.P1.Geometry.prefixEnd<zW := by
  have hz : 732/1000<zW := by
    have hg : 0<GW := by linarith [GW_bounds.1]
    unfold zW
    rw [lt_div_iff₀ hg]
    nlinarith [GW_bounds.2]
  have hp : polyak.Certificates.Continuation.P1.Geometry.prefixEnd<(732/1000 : ℝ) := by
    norm_num [polyak.Certificates.Continuation.P1.Geometry.prefixEnd]
  exact hp.trans hz

theorem continuation_atomFactor_slope {z : ℝ}
    (hz : z∈Set.Ioo polyak.Certificates.Continuation.P1.Geometry.prefixEnd zW) :
    continuation z 1+z*deriv continuation z 1<0 := by
  have hzO : z∈Set.Ioo (0 : ℝ) (733/1000) :=
    ⟨prefixEnd_pos.trans hz.1,hz.2.trans zW_bounds.2⟩
  have hzD : z∈continuationDomain := ⟨hzO.1.le,hzO.2.le⟩
  have htail : z∈Set.Icc ((7306177500000001/10000000000000000 : ℚ) : ℝ) ((733/1000 : ℚ) : ℝ) := by
    norm_num
    constructor
    · have hp:=hz.1
      norm_num [polyak.Certificates.Continuation.P1.Geometry.prefixEnd] at hp
      linarith
    · exact hzO.2.le
  obtain ⟨slab,hm,hs⟩ := coverCheck_sound _ _ _
    polyak.Certificates.Continuation.P1.Geometry.tailCovered htail
  have hm' := polyak.Certificates.Continuation.P1.Geometry.tailSlabs_subset hm
  have hc := List.all_eq_true.mp polyak.Certificates.Continuation.P1.Geometry.slopeAccepted slab hm
  exact geometrySlopeCheck_sound polyak.Certificates.Continuation.P1.system
    (fun i => ((polyak.Certificates.Continuation.P1.system i).checkADSupported_eq_true_iff).mp
      (polyak.Certificates.Continuation.P1.check_supported i)) _ _ _ hc hs
    (continuation_mem_box hzD hm' hs) (continuation_derivative_equation hzO)

theorem continuation_atomFactor_nonneg {z : ℝ} (hz : z∈Set.Icc (0 : ℝ) zW) :
    0≤atomFactor continuation z := by
  have hzD : z∈continuationDomain := ⟨hz.1,hz.2.trans zW_bounds.2.le⟩
  by_cases hp : z≤polyak.Certificates.Continuation.P1.Geometry.prefixEnd
  · have hprefix : z∈Set.Icc ((0 : ℚ) : ℝ)
        ((7311675000000001/10000000000000000 : ℚ) : ℝ) := by
      simpa only [Set.mem_Icc,polyak.Certificates.Continuation.P1.Geometry.prefixEnd,Rat.cast_div,
        Rat.cast_ofNat,Rat.cast_zero] using And.intro hz.1 hp
    obtain ⟨slab,hm,hs⟩ := coverCheck_sound _ _ _
      polyak.Certificates.Continuation.P1.Geometry.atomCovered hprefix
    have hm' := polyak.Certificates.Continuation.P1.Geometry.atomSlabs_subset hm
    exact allAtomCheck_sound polyak.Certificates.Continuation.P1.Geometry.atomAccepted hm hs
      (continuation_mem_box hzD hm' hs)
  · have hsub : Set.Icc polyak.Certificates.Continuation.P1.Geometry.prefixEnd zW⊆continuationDomain := by
      intro r hr
      exact ⟨prefixEnd_pos.le.trans hr.1,hr.2.trans zW_bounds.2.le⟩
    have hg := continuation_continuousOn.mono hsub
    have hB : ContinuousOn (fun r => continuation r 1)
        (Set.Icc polyak.Certificates.Continuation.P1.Geometry.prefixEnd zW) :=
      (ContinuousLinearMap.proj (1 : Fin 2) : Coordinates →L[ℝ] ℝ).continuous.comp_continuousOn hg
    apply atomFactor_nonneg_before_endpoint (continuousOn_const.add (continuousOn_id.mul hB))
      ?_ prefixEnd_lt_zW.le (atomFactor_endpoint continuation_endpoint) ⟨(lt_of_not_ge hp).le,hz.2⟩
    intro r hr
    have hrO : r∈Set.Ioo (0 : ℝ) (733/1000) :=
      ⟨prefixEnd_pos.trans hr.1,hr.2.trans zW_bounds.2⟩
    exact ⟨deriv continuation r,(continuation_analyticAt hrO).differentiableAt.hasDerivAt,
      continuation_atomFactor_slope hr⟩

/-- Every positive point up to the exact radical switch has all physical source reserves. -/
theorem continuation_physical {z : ℝ} (hz : z∈Set.Ioc (0 : ℝ) zW) :
    PhysicalBounds z (continuation z) :=
  (continuation_core ⟨hz.1.le,hz.2.trans zW_bounds.2.le⟩).with_atom_lower
    (atom_lower_of_factor_nonneg hz.1.le (continuation_atomFactor_nonneg ⟨hz.1.le,hz.2⟩))

/-- The actual infinite feasible spectrum on the entire physical P1 arc. -/
theorem continuation_feasible {z t : ℝ} (hz : z∈Set.Ioc (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) :
    Spectral.FeasibleU (branchU z (continuation z 0)) t
      (spectrum (physicalAtom hz.1 (by linarith [hz.2,zW_bounds.2]) (continuation_physical hz)))
      (chargeNumerator z (branchU z (continuation z 0)) (branchAtom z (continuation z 1))/Real.sinh t) :=
  regularRoot_feasible hz.1 (by linarith [hz.2,zW_bounds.2])
    (continuation_source ⟨hz.1.le,hz.2.trans zW_bounds.2.le⟩) (continuation_physical hz) ht

/-- The full source proposition: actual V is identified throughout the closed physical P1 arc. -/
theorem continuation_optimal {z t : ℝ} (hz : z∈Set.Ioc (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) :
    Spectral.V t=Real.arsinh (branchU z (continuation z 0)) :=
  regularRoot_optimal hz.1 (by linarith [hz.2,zW_bounds.2])
    (continuation_source ⟨hz.1.le,hz.2.trans zW_bounds.2.le⟩) (continuation_physical hz) ht

/-- Strict spiral suboptimality on the full open P1 regime. -/
theorem continuation_strict_spiral {z t : ℝ} (hz : z∈Set.Ioo (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) : Real.arsinh (1-1/(2*Real.cosh t))<Spectral.V t :=
  regularRoot_strict_spiral hz.1 (by linarith [hz.2,zW_bounds.2])
    (continuation_source ⟨hz.1.le,(hz.2.trans zW_bounds.2).le⟩)
    (continuation_physical ⟨hz.1,hz.2.le⟩) ht hz.2.ne

/-- The global checked regime agrees with the independently derived critical IFT expansion. -/
theorem V_eq_localU_eventually :
    ∀ᶠ z in 𝓝[Set.Ioi (0 : ℝ)] 0, ∀ t : ℝ, Real.cosh t=1/z →
      Spectral.V t=Real.arsinh (localU z) := by
  have hn : ∀ᶠ z in 𝓝 (0 : ℝ), z<zW := gt_mem_nhds zW_pos
  filter_upwards [continuation_eq_localBranch.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z he hzW hz0
  intro t ht
  have hzD : z∈continuationDomain := ⟨hz0.le,(hzW.trans zW_bounds.2).le⟩
  rw [continuation_optimal ⟨hz0,hzW.le⟩ ht,he hzD]
  rfl

end polyak.Boundary.P1
