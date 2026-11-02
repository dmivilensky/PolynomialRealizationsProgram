import jacobi.Oscillation.PhaseRepresentation
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Proposition B.1.
The actual phase integral has exactly the original solution zeros. Between
consecutive original zeros with positive phase speed its true increment
is precisely pi. Both claims are derived from the constructed rotation
representation and the intermediate value theorem.
Use: the zero-level count used in McMahon and the uniform Jacobi phase comparison concerns the actual source functions.
-/
namespace jacobi.Oscillation.RestoringSolution
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {I : Set ℝ} (S : RestoringSolution I)

/-- The constructed genuine continuous phase has exactly the original solution zeros when based at an actual solution zero.
Use: the zero-level count used in McMahon and the uniform Jacobi phase comparison concerns the actual source functions.
Article: jacobi, Proposition B.1.
Proof: at the original base zero the actual normalized sine vanishes and
its cosine square equals one. The proved rotating-state representation
therefore makes the actual normalized value a nonzero constant times the
sine of the constructed integral phase. The positive amplitude preserves zeros. -/
theorem value_zero_iff_phase (hIo : IsOpen I) (hI : Convex ℝ I) {base x : ℝ}
    (hb : base∈I) (hx : x∈I) (hzero : S.value base=0) :
    S.value x=0 ↔ sin (S.phase base x)=0 := by
  -- The genuine initial zero fixes the angle branch; no phase/zero correspondence is supplied as a separate premise.
  have hsb : S.unitSin base=0 := by simp only [unitSin,hzero,zero_div]
  have hcb : S.unitCos base≠0 := by
    have hcircle := S.unit_circle hb
    rw [hsb,zero_pow (by norm_num : 2≠0),add_zero] at hcircle
    intro h
    rw [h,zero_pow (by norm_num : 2≠0)] at hcircle
    norm_num at hcircle
  have hrep := (S.phase_representation hIo hI hb hx).2
  rw [hsb,zero_mul,zero_add] at hrep
  constructor
  · intro hz
    have hsx : S.unitSin x=0 := by simp only [unitSin,hz,zero_div]
    rw [hsx] at hrep
    exact (mul_eq_zero.mp hrep.symm).resolve_left hcb
  · intro hz
    have hsx : S.unitSin x=0 := by rw [hrep,hz,mul_zero]
    have hc := div_mul_cancel₀ (S.value x) (S.amplitude_pos hx).ne'
    change S.unitSin x*S.amplitude x=S.value x at hc
    rw [hsx,zero_mul] at hc
    exact hc.symm

/-- A phase based at an actual solution zero has the exact original restoring speed written in its actual sine coordinate.
Use: gives the genuine inverse-square Bessel phase equation and the finite Jacobi perturbation equation in the same normalization.
Article: jacobi, Proposition B.1.
Proof: the actual base sine coordinate vanishes and its cosine square is
one. Substitute the proved genuine rotation representation into the exact
original normalized-state speed identity. -/
theorem phaseDensity_at_zero (hIo : IsOpen I) (hI : Convex ℝ I) {base x : ℝ}
    (hb : base∈I) (hx : x∈I) (hzero : S.value base=0) :
    S.phaseDensity x=1+(S.potential x-1)*sin (S.phase base x)^2 := by
  have hsb : S.unitSin base=0 := by simp only [unitSin,hzero,zero_div]
  have hcb := S.unit_circle hb
  rw [hsb,zero_pow (by norm_num : 2≠0),add_zero] at hcb
  have hrep := (S.phase_representation hIo hI hb hx).2
  rw [hsb,zero_mul,zero_add] at hrep
  rw [S.phaseDensity_eq hx,hrep,mul_pow,hcb,one_mul]

/-- Positive actual phase speed makes the constructed integral phase strictly increasing on each physical convex comparison interval.
Use: no source zero level is skipped or counted twice when the actual consecutive-zero increment is identified.
Article: jacobi, Proposition B.1.
Proof: use the genuine phase derivative and the community strict mean-value theorem on the specified convex interval. -/
theorem phase_strictMonoOn (hI : Convex ℝ I) {J : Set ℝ} (hJ : Convex ℝ J) (hJI : J⊆I)
    {base : ℝ} (hb : base∈I) (hp : ∀ x∈J,0<S.phaseDensity x) : StrictMonoOn (S.phase base) J := by
  apply strictMonoOn_of_deriv_pos hJ
    (fun x hx => (S.phase_hasDerivAt hI hb (hJI hx)).continuousAt.continuousWithinAt)
  intro x hx
  rw [(S.phase_hasDerivAt hI hb (hJI (interior_subset hx))).deriv]
  exact hp x (interior_subset hx)

/-- Between consecutive actual original zeros the true positive-speed phase increment is exactly pi.
Use: identifies the actual indexed phase constants used in the McMahon remainder and in the uniform finite zero comparison.
Article: jacobi, Proposition B.1.
Proof: the sine of the endpoint phase difference is zero and the true
phase strictly increases, so the difference is at least pi. A difference
larger than pi would cross the next sine-zero level at an interior point
by the intermediate value theorem, contradicting the actual zero-free
nodal interval of the original solution. -/
theorem phase_increment_between_zeros (hIo : IsOpen I) (hI : Convex ℝ I)
    {base a b : ℝ} (hb0 : base∈I) (hbase : S.value base=0)
    (ha : a∈I) (hb : b∈I) (hab : a<b) (hfa : S.value a=0) (hfb : S.value b=0)
    (hne : ∀ x∈Ioo a b,S.value x≠0)
    (hp : ∀ x∈Icc a b,0<S.phaseDensity x) : S.phase base b-S.phase base a=Real.pi := by
  -- Both endpoint phase levels and the exclusion of an intermediate phase zero refer to the actual original solution.
  have hJI : Icc a b⊆I := fun x hx => hI.ordConnected.uIcc_subset ha hb (Icc_subset_uIcc hx)
  have hm := S.phase_strictMonoOn hI (convex_Icc a b) hJI hb0 hp
  have hlt := hm ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab
  have hsa := (S.value_zero_iff_phase hIo hI hb0 ha hbase).mp hfa
  have hsb := (S.value_zero_iff_phase hIo hI hb0 hb hbase).mp hfb
  have hs : sin (S.phase base b-S.phase base a)=0 := by
    rw [Real.sin_sub,hsb,hsa,zero_mul,mul_zero,sub_self]
  have hlo : Real.pi≤S.phase base b-S.phase base a := by
    by_contra hn
    exact (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt) (not_le.mp hn)).ne' hs
  have hhi : S.phase base b-S.phase base a≤Real.pi := by
    by_contra hn
    have hgt : Real.pi<S.phase base b-S.phase base a := not_le.mp hn
    have hc : ContinuousOn (S.phase base) (Icc a b) := fun x hx =>
      (S.phase_hasDerivAt hI hb0 (hJI hx)).continuousAt.continuousWithinAt
    obtain ⟨x,hx,he⟩ := intermediate_value_Icc hab.le hc
      (show S.phase base a+Real.pi∈Icc (S.phase base a) (S.phase base b) from
        ⟨by linarith [Real.pi_pos],by linarith⟩)
    have hxa : x≠a := by intro hh; rw [hh] at he; linarith [Real.pi_pos]
    have hxb : x≠b := by intro hh; rw [hh] at he; linarith
    apply hne x ⟨lt_of_le_of_ne hx.1 hxa.symm,lt_of_le_of_ne hx.2 hxb⟩
    apply (S.value_zero_iff_phase hIo hI hb0 (hJI hx) hbase).mpr
    rw [he,Real.sin_add_pi,hsa,neg_zero]
  exact le_antisymm hhi hlo

end
end jacobi.Oscillation.RestoringSolution
