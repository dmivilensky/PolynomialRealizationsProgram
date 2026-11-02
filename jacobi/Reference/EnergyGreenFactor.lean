import jacobi.Reference.EnergyWronskian

/-!
Article: jacobi, Proposition C.4.
The selected left/right factor has its exact original Fourier
coefficients at every real energy below the first reference eigenvalue.
The original singular Green identity and reference reflection discharge
both endpoint terms. This specializes at E=0 to the source Green lemma.
Use: energyGreen_factorization identifies this expression with the full original spectral series at zero energy.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original selected left/right Green factor at real energy E.
Use: energyGreen_factorization identifies this expression with the full original spectral series at zero energy.
Article: jacobi, Proposition C.4.
-/
def energyGreenFactor (a E t s : ℝ) : ℝ :=
  realSolution a E (min t s)*realSolution a E (1-max t s)/energyGreenConstant a E

attribute [local irreducible] energyGreenFactor energyGreenConstant realSolution solution

/-- Every actual selected-solution Green row with an interior source is continuous on the whole closed original unit interval.
Use: the full coefficient identity and the actual continuous L2 embedding imply pointwise Green factorization, including both physical endpoints.
Article: jacobi, Proposition C.4.
Proof: the minimum keeps the left selected argument below s<1, while the reflected maximum keeps the right selected argument below 1-s<1. Both arguments stay nonnegative, so genuine endpoint-inclusive original joint continuity applies everywhere on the closed row. -/
theorem energyGreenFactor_continuousOn {a E s : ℝ} (ha : -1<a) (hs : s∈Ioo (0:ℝ) 1) :
    ContinuousOn (fun t => energyGreenFactor a E t s) (Icc (0:ℝ) 1) := by
  -- Neither unreflected selected solution is evaluated at its opposite singular endpoint.
  unfold energyGreenFactor
  intro t ht
  have hl : min t s∈Ico (0:ℝ) 1 := ⟨le_min ht.1 hs.1.le,(min_le_right t s).trans_lt hs.2⟩
  have hr : 1-max t s∈Ico (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (max_le ht.2 hs.2.le),by linarith [le_max_right t s,hs.1]⟩
  have hc (E x : ℝ) (hx : x∈Ico (0:ℝ) 1) : ContinuousAt (realSolution a E) x := by
    unfold realSolution
    have hpair : ContinuousAt (fun y : ℝ => (y,(E:ℂ))) x :=
      continuousAt_id.prodMk continuousAt_const
    have hcc : ContinuousAt (fun y : ℝ => solution a (E:ℂ) y) x :=
      (solution_joint_continuous ha hx (E:ℂ)).comp_of_eq hpair rfl
    exact Complex.continuous_re.continuousAt.comp hcc
  have hmin : ContinuousAt (fun x : ℝ => min x s) t := continuousAt_id.min continuousAt_const
  have hmax : ContinuousAt (fun x : ℝ => 1-max x s) t :=
    continuousAt_const.sub (continuousAt_id.max continuousAt_const)
  have hleft : ContinuousAt (fun x : ℝ => realSolution a E (min x s)) t :=
    (hc _ _ hl).comp_of_eq hmin rfl
  have hright : ContinuousAt (fun x : ℝ => realSolution a E (1-max x s)) t :=
    (hc _ _ hr).comp_of_eq hmax rfl
  exact (hleft.mul hright).div_const _ |>.continuousWithinAt

/-- The selected-solution Green row is a genuine continuous function on the same full interval as the reference Hilbert basis.
Use: energyGreen_factorization_interior compares its proved coefficients with the continuous Green-row series in the actual L2 space, then continuous representatives give pointwise equality.
Article: jacobi, Proposition C.4.
-/
def energyGreenFactorRow (a E : ℝ) (ha : -1<a) (s : ℝ) (hs : s∈Ioo (0:ℝ) 1) : C(Interval,ℝ) :=
  ⟨fun t => energyGreenFactor a E t s,(energyGreenFactor_continuousOn (E := E) ha hs).comp_continuous
    continuous_subtype_val (fun t => t.property)⟩

/-- The original Green identity at real energy E holds with the genuine real solutions and their actual real slopes.
Use: computes both halves of every coefficient of energyGreenFactorRow, discharging the normalization in the complete spectral Green factorization.
Article: jacobi, Proposition C.4.
Proof: specialize the proved complex Green identity to the two original real energies, convert the actual integral to the inclusion of its real integral, and use the independently proved reality of the genuine spatial slopes. -/
theorem reference_real_green_identity {a E t : ℝ} (ha : -1<a) (k : ℕ) (ht : t∈Ioo (0:ℝ) 1) :
    (eigenvalue a k-E)*
      (∫ x in (0:ℝ)..t,realSolution a (eigenvalue a k) x*realSolution a E x)=
      realSolution a (eigenvalue a k) t*realSlope a E t-
        realSlope a (eigenvalue a k) t*realSolution a E t := by
  -- Every slope in this identity is the already proved actual spatial derivative.
  have hh := reference_green_identity ha (eigenvalue a k:ℂ) (E:ℂ) ht
  have hi : (∫ x in (0:ℝ)..t,solution a (eigenvalue a k:ℂ) x*solution a (E:ℂ) x)=
      ((∫ x in (0:ℝ)..t,realSolution a (eigenvalue a k) x*realSolution a E x):ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only
    rw [Complex.ofReal_mul,realSolution_cast,realSolution_cast]
  have he : (eigenvalue a k:ℂ)-(E:ℂ)=((eigenvalue a k-E):ℝ) := by
    push_cast
    rfl
  have hw : referenceWronskian a (eigenvalue a k:ℂ) (E:ℂ) t=
      ((realSolution a (eigenvalue a k) t*realSlope a E t-
        realSlope a (eigenvalue a k) t*realSolution a E t:ℝ):ℂ) := by
    simp only [referenceWronskian,Complex.ofReal_sub,Complex.ofReal_mul,realSolution_cast,realSlope,
      solutionSlope_real a (eigenvalue a k) ht,solutionSlope_real a (E) ht]
  rw [hi,he,hw,← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh


/-- The actual selected-solution Green factor has exactly its original reference Fourier coefficient.
Use: energyGreen_factorization invokes the proved complete reference Hilbert expansion and genuine continuous-function norm summability to identify the factor with the original Green series pointwise.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: split the genuine integral at s, reflect the right interval, and apply the independently proved zero-endpoint Green identity on each half. Exact solution and slope parity makes the two boundary terms combine into the actual nonzero constant W_E. -/
theorem energyGreenFactor_coefficient {a E s : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0) (hs : s∈Ioo (0:ℝ) 1) (k : ℕ) :
    (eigenvalue a k-E)*
      (∫ t in (0:ℝ)..1,energyGreenFactor a E t s*eigenfunction a k t)=eigenfunction a k s := by
  -- Both integrals are genuine convergent integrals of the original continuous patched factor.
  have hc : ContinuousOn (fun t : ℝ => energyGreenFactor a E t s*eigenfunction a k t) (Icc (0:ℝ) 1) :=
    (energyGreenFactor_continuousOn (E := E) ha hs).mul (eigenfunction_properties ha k).1.continuousOn
  have hleft : (∫ t in (0:ℝ)..s,energyGreenFactor a E t s*eigenfunction a k t)=
      realSolution a E (1-s)/energyGreenConstant a E*
        (∫ t in (0:ℝ)..s,realSolution a (eigenvalue a k) t*realSolution a E t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hs.1.le] at ht
    rw [energyGreenFactor,min_eq_left ht.2,max_eq_right ht.2,realSolution_at_reference]
    ring
  have hright : (∫ t in s..1,energyGreenFactor a E t s*eigenfunction a k t)=
      realSolution a E s/energyGreenConstant a E*(-1:ℝ)^k*
        (∫ t in (0:ℝ)..(1-s),realSolution a (eigenvalue a k) t*realSolution a E t) := by
    rw [← intervalIntegral.integral_const_mul]
    have he : (∫ t in s..1,energyGreenFactor a E t s*eigenfunction a k t)=
        ∫ t in s..1,(realSolution a E s/energyGreenConstant a E*(-1:ℝ)^k)*
          (realSolution a (eigenvalue a k) (1-t)*realSolution a E (1-t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [uIcc_of_le hs.2.le] at ht
      rw [energyGreenFactor,min_eq_right ht.1,max_eq_left ht.1,realSolution_at_reference,
        eigenfunction_reflection ha]
      have heven : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
      linear_combination - (realSolution a E s/energyGreenConstant a E*
        eigenfunction a k t*realSolution a E (1-t))*heven
    rw [he]
    simpa only [sub_self,sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => (realSolution a E s/energyGreenConstant a E*(-1:ℝ)^k)*
          (realSolution a (eigenvalue a k) x*realSolution a E x)) (a := s) (b := 1) 1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le)
    ((hc.mono (Icc_subset_Icc hs.1.le le_rfl)).intervalIntegrable_of_Icc hs.2.le),hleft,hright]
  have hL := reference_real_green_identity (E := E) ha k hs
  have hr : 1-s∈Ioo (0:ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hR := reference_real_green_identity (E := E) ha k hr
  have hW := energyGreenConstant_at (E := E) ha hs
  simp only [realSolution_at_reference,eigenfunction_reflection ha,
    realSlope_reference_reflection ha k hs] at hL hR
  have hp : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
  have hWne := energyGreenConstant_ne_zero ha hE
  simp only [realSolution_at_reference]
  field_simp [hWne]
  linear_combination
    realSolution a E (1-s)*hL+
    realSolution a E s*(-1:ℝ)^k*hR+
    eigenfunction a k s*hW+
    (realSolution a E s*eigenfunction a k s*
      realSlope a E (1-s)+
    realSolution a E s*realSolution a E (1-s)*
      realSlope a (eigenvalue a k) s)*hp


end
end jacobi.Reference
