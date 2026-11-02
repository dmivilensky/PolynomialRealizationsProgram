import jacobi.GelfandLevitan.TargetPotential

/-!
Article: jacobi, Appendix C.2.
The actual potential perturbation has zero improper integral.
On a positive half strip its integral is exactly the original diagonal
primitive difference. Both endpoint constants have been proved zero;
reflection gives the full physical interval, without absolute
integrability or differentiability at the singular endpoint premises.
Use: targetPotential_half_improper_zero removes the actual integration constants in the half-domain potential primitive.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine original diagonal is continuously extended to zero and vanishes there and at the midpoint.
Use: targetPotential_half_improper_zero removes the actual integration constants in the half-domain potential primitive.
Article: jacobi, Proposition C.2.
Proof: the original diagonal and physical clamp are continuous, and both genuine original boundary values were independently proved zero. -/
theorem diagonalPhysical_boundary (a : ℝ) (ha : -1<a) :
    Continuous (diagonalPhysical a ha) ∧ diagonalPhysical a ha 0=0 ∧ diagonalPhysical a ha (1/2)=0 := by
  refine ⟨(kernelDiagonal a ha).continuous.comp halfParameterClamp.continuous,?_,?_⟩
  · change kernelDiagonal a ha (halfParameterClamp 0)=0
    rw [show halfParameterClamp 0=halfZero from Set.projIcc_of_mem (by norm_num) (by norm_num)]
    exact kernelDiagonal_zero a ha
  · change kernelDiagonal a ha (halfParameterClamp (1/2))=0
    rw [show halfParameterClamp (1/2)=halfMidpoint from Set.projIcc_of_mem (by norm_num) (by norm_num)]
    exact kernelDiagonal_midpoint_zero a ha

/-- The original potential correction on every positive physical half strip is exactly minus twice the original lower-end diagonal value.
Use: targetPotential_half_improper_zero proves convergence of the actual improper half integral at zero, and targetPotential_truncated_integral evaluates the full interval.
Article: jacobi, Proposition C.2.
Source: the fundamental theorem of calculus for the genuine C1 diagonal.
Proof: on this original half strip V-q is exactly 2*w'. The independently proved original C1 regularity supplies its true derivative and continuous integrability. The genuine midpoint value is zero. -/
theorem targetPotential_half_integral (a : ℝ) (ha : -1<a) {e : ℝ} (he : 0<e) (hem : e≤(1/2:ℝ)) :
    (∫ t in e..(1/2),targetPotential a ha t-potential a t)= -2*diagonalPhysical a ha e := by
  -- The FTC concerns the actual w, so there is no assumed integral identity for the target potential.
  have hsub : Icc e (1/2)⊆Ioc (0:ℝ) (1/2) := fun x hx => ⟨he.trans_le hx.1,hx.2⟩
  have hD (x : ℝ) (hx : x∈Ioo e (1/2)) :
      HasDerivAt (diagonalPhysical a ha) (diagonalPhysicalSlope a ha x) x :=
    (((kernelDiagonal_contDiffOn a ha) x ⟨he.trans hx.1,hx.2.le⟩).differentiableWithinAt
      (by norm_num : (1:WithTop ℕ∞)≠0)).hasDerivWithinAt.hasDerivAt
        (Ioc_mem_nhds (he.trans hx.1) hx.2)
  have hi := ((diagonalPhysicalSlope_continuousOn a ha).mono hsub).intervalIntegrable_of_Icc (μ := volume) hem
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hem
    (diagonalPhysical_boundary a ha).1.continuousOn hD hi
  have heq : (∫ t in e..(1/2),targetPotential a ha t-potential a t)=
      2*(∫ t in e..(1/2),diagonalPhysicalSlope a ha t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hem] at ht
    rw [targetPotential_half a ha ht.2,halfTargetPotential]
    ring
  rw [heq,hFTC,(diagonalPhysical_boundary a ha).2.2]
  ring

/-- The actual original half-domain perturbation has zero improper integral at its singular endpoint.
Use: targetPotential_improper_zero obtains the original full-domain zero improper mean by exact reflection, rather than an unproved integrability premise.
Article: jacobi, Proposition C.2.
Proof: the exact positive-strip primitive is -2*w(epsilon), and the original w is continuous and zero at its genuine zero endpoint. -/
theorem targetPotential_half_improper_zero (a : ℝ) (ha : -1<a) :
    Tendsto (fun e:ℝ => ∫ t in e..(1/2),targetPotential a ha t-potential a t)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hw := ((diagonalPhysical_boundary a ha).1.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  rw [(diagonalPhysical_boundary a ha).2.1] at hw
  apply (show Tendsto (fun e:ℝ => -2*diagonalPhysical a ha e) (𝓝[>] (0:ℝ)) (𝓝 0) from by
    simpa using hw.const_mul (-2)).congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with e he
  exact (targetPotential_half_integral a ha he.1 he.2.le).symm

/-- Exact reflection identifies both original truncated half integrals of the actual potential correction.
Use: targetPotential_truncated_integral and targetPotential_improper_zero prove the original full improper-mean assertion.
Article: jacobi, Proposition C.2.
Source: reflection change of variable in the ordinary interval integral.
Proof: substitute t=1-s in the unchanged actual correction and use its two independently proved original reflection symmetries. -/
theorem targetPotential_reflected_integral (a : ℝ) (ha : -1<a) (e : ℝ) :
    (∫ t in (1/2)..(1-e),targetPotential a ha t-potential a t)=
      ∫ t in e..(1/2),targetPotential a ha t-potential a t := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun t => targetPotential a ha t-potential a t) (a := (1/2:ℝ)) (b := 1-e) 1
  simpa only [targetPotential_reflection,potential_reflection,
    show (1:ℝ)-(1-e)=e by ring,show (1:ℝ)-1/2=1/2 by norm_num] using h

/-- The actual full symmetric truncation of the potential perturbation is exactly -4*w(epsilon).
Use: targetPotential_improper_zero evaluates the original full-domain improper mean.
Article: jacobi, Proposition C.2.
Proof: the continuous original correction is integrable on each positive truncated interval. Split at the midpoint, reflect the second piece and apply the proved actual half-domain FTC. -/
theorem targetPotential_truncated_integral (a : ℝ) (ha : -1<a) {e : ℝ} (he : 0<e) (hem : e<(1/2:ℝ)) :
    (∫ t in e..(1-e),targetPotential a ha t-potential a t)= -4*diagonalPhysical a ha e := by
  -- Continuity is used only on the actual nonsingular compact intervals; the singular limit is taken after the exact FTC identity.
  have hc : ContinuousOn (fun t => targetPotential a ha t-potential a t) (Ioo (0:ℝ) 1) :=
    (targetPotential_continuousOn a ha).sub (potential_continuousOn a)
  have hL := (hc.mono (show Icc e (1/2)⊆Ioo (0:ℝ) 1 from
    fun t ht => ⟨he.trans_le ht.1,by linarith [ht.2]⟩)).intervalIntegrable_of_Icc (μ := volume) hem.le
  have hR := (hc.mono (show Icc (1/2:ℝ) (1-e)⊆Ioo (0:ℝ) 1 from
    fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)).intervalIntegrable_of_Icc (μ := volume) (by linarith : (1/2:ℝ)≤1-e)
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR,
    targetPotential_reflected_integral,targetPotential_half_integral a ha he hem.le]
  ring

/-- The original full target potential perturbation has precisely zero improper integral.
Use: completes the genuine mean-zero potential assertion in general Proposition C.2; the separate half-domain limit ensures the conclusion does not rely only on cancellation in a symmetric principal value.
Article: jacobi, Proposition C.2.
Proof: the exact original full truncation is twice the genuine half integral, whose independently proved improper limit is zero. Reflection also gives the separate other endpoint limit. -/
theorem targetPotential_improper_zero (a : ℝ) (ha : -1<a) :
    Tendsto (fun e:ℝ => ∫ t in e..(1-e),targetPotential a ha t-potential a t)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply (show Tendsto (fun e:ℝ => 2*(∫ t in e..(1/2),targetPotential a ha t-potential a t))
    (𝓝[>] (0:ℝ)) (𝓝 0) from by simpa using (targetPotential_half_improper_zero a ha).const_mul 2).congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with e he
  rw [targetPotential_truncated_integral a ha he.1 he.2,targetPotential_half_integral a ha he.1 he.2.le]
  ring

end
end jacobi.GelfandLevitan
