import polyak.Boundary.P1.DerivativeContinuation

/-!
Article: Proposition P₁ in full, including the physical endpoint.
Use: one source-facing result gathers the actual feasible/optimal spectrum,
quantitative minimizer reserve, strict source geometry and the actual derivative bounds.
-/
noncomputable section
namespace polyak.Boundary.P1
open Set Filter Spectral
open scoped Topology ContDiff

def continuedAtom (z : ℝ) : ℝ := branchAtom z (continuation z 1)
def continuedCharge (z t : ℝ) : ℝ := chargeNumerator z (continuedU z) (continuedAtom z)/Real.sinh t

theorem continuedU_continuousOn : ContinuousOn continuedU (Icc (0 : ℝ) zW) := by
  have hg:=continuation_continuousOn.mono (show Icc (0 : ℝ) zW⊆continuationDomain from
    fun z hz => ⟨hz.1,hz.2.trans zW_bounds.2.le⟩)
  have hA : ContinuousOn (fun z => continuation z 0) (Icc (0 : ℝ) zW) :=
    (ContinuousLinearMap.proj (0 : Fin 2) : Coordinates →L[ℝ] ℝ).continuous.comp_continuousOn hg
  unfold continuedU branchU
  fun_prop

/-- The actual source u decreases strictly in z, including both finite endpoints. -/
theorem continuedU_strictAntiOn : StrictAntiOn continuedU (Icc (0 : ℝ) zW) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _ ) continuedU_continuousOn
  intro z hz
  rw [interior_Icc] at hz
  have hzm : z∈Ioo (0 : ℝ) (733/1000) := ⟨hz.1,hz.2.trans zW_bounds.2⟩
  rw [(continuedU_hasDerivAt hzm).deriv]
  exact (continuedU_derivative_bounds hzm).1

/-- Strict source bounds on the whole physical closed-at-the-switch branch. -/
theorem continuedU_bounds {z : ℝ} (hz : z∈Ioc (0 : ℝ) zW) : 1/2<continuedU z ∧ continuedU z<1 := by
  have h0 : continuedU 0=1 := by simp [continuedU,branchU]
  have hW : continuedU zW=1-zW/2 := by
    unfold continuedU
    rw [continuation_endpoint,endpoint_u]
  have hl:=continuedU_strictAntiOn.antitoneOn ⟨hz.1.le,hz.2⟩ ⟨zW_pos.le,le_rfl⟩ hz.2
  have hu:=continuedU_strictAntiOn ⟨le_rfl,zW_pos.le⟩ ⟨hz.1.le,hz.2⟩ hz.1
  rw [h0] at hu
  rw [hW] at hl
  exact ⟨by linarith [zW_bounds.2],hu⟩

/-- The source atom is strictly negative; zero would contradict the derivative contact. -/
theorem continuedAtom_bounds {z : ℝ} (hz : z∈Ioc (0 : ℝ) zW) :
    -z/2≤continuedAtom z ∧ continuedAtom z<0 := by
  have hp:=continuation_physical hz
  have hcontacts:=regularSystem_contacts (continuation_source
    ⟨hz.1.le,hz.2.trans zW_bounds.2.le⟩)
  refine ⟨hp.atom_lower,lt_of_le_of_ne hp.atom_nonpos ?_⟩
  intro hzero
  change continuedAtom z=0 at hzero
  have hder : quarticDerivative z (continuedU z) (continuedAtom z)=0 := hcontacts.2
  have hcontact : quartic z (continuedU z) (continuedAtom z)=0 := hcontacts.1
  rw [hzero] at hder
  rw [hzero] at hcontact
  have hid : z*quartic z (continuedU z) 0-
      (2-z^2)*quarticDerivative z (continuedU z) 0=
        -2*continuedU z*z^2*(1-z^2) := by unfold quartic quarticDerivative; ring
  rw [hcontact,hder] at hid
  have hupos:=(continuedU_bounds hz).1
  have hu0 : 0<continuedU z := by linarith
  have hzz : 0<1-z^2 := by nlinarith [hz.1,hz.2,zW_bounds.2]
  have hpos : 0<2*continuedU z*z^2*(1-z^2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hu0) (sq_pos_of_pos hz.1)) hzz
  nlinarith

/-- The branch u₁ increases strictly with the physical parameter G. -/
def uOfG (G : ℝ) : ℝ := continuedU (1/G)

theorem uOfG_strictMonoOn : StrictMonoOn uOfG (Ici GW) := by
  intro G hG K hK hGK
  change GW≤G at hG
  change GW≤K at hK
  have hGp : 0<G := by linarith [GW_bounds.1,hG]
  have hKp : 0<K := hGp.trans hGK
  have hzG : 1/G∈Icc (0 : ℝ) zW :=
    ⟨(one_div_pos.mpr hGp).le,one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hG⟩
  have hzK : 1/K∈Icc (0 : ℝ) zW :=
    ⟨(one_div_pos.mpr hKp).le,one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hK⟩
  exact continuedU_strictAntiOn hzK hzG (one_div_lt_one_div_of_lt hGp hGK)

/-- Proposition P₁: all physical, primal, dual, quantitative and derivative conclusions
for the actual globally continued source branch; every lag is included in FeasibleU. -/
theorem p1_point {z t : ℝ} (hz : z∈Ioc (0 : ℝ) zW) (ht : Real.cosh t=1/z) :
    (∃ ν : Spectrum,FeasibleU (continuedU z) t ν (continuedCharge z t)) ∧
    V t=Real.arsinh (continuedU z) ∧
    (-z/2≤continuedAtom z ∧ continuedAtom z<0) ∧
    z^3/4≤1-(continuedAtom z)^2-(continuedU z)^2-|continuedCharge z t| ∧
    (∀ c : ℝ,quartic z (continuedU z) c=(c-continuedAtom z)^2*
      (z^2*c^2+residualLinear z (continuedU z) (continuedAtom z)*c+
        residualConstant z (continuedU z) (continuedAtom z))) ∧
    0<residualConstant z (continuedU z) (continuedAtom z)-
      |residualLinear z (continuedU z) (continuedAtom z)| ∧
    (1/2<continuedU z ∧ continuedU z<1) ∧
    (continuedUDerivative z<0 ∧
      (continuedUDerivative z)^2*z^2*(1-z^2)<1+(continuedU z)^2) ∧
    (z<zW → |deriv V t|<1) := by
  have hzm : z≤3/4 := by linarith [hz.2,zW_bounds.2]
  have hp:=continuation_physical hz
  have hc:=regularSystem_contacts (continuation_source ⟨hz.1.le,hz.2.trans zW_bounds.2.le⟩)
  refine ⟨⟨_,continuation_feasible hz ht⟩,continuation_optimal hz ht,continuedAtom_bounds hz,
    minimizer_gap hz.1 hzm ⟨hp.atom_lower,hp.atom_nonpos⟩ hp.u_nonneg hp.gap_lower hc.1 ht,
    ?_,?_,continuedU_bounds hz,continuedU_derivative_bounds ⟨hz.1,hz.2.trans_lt zW_bounds.2⟩,
    fun h => abs_deriv_V_lt_one ⟨hz.1,h⟩ ht⟩
  · intro c
    exact quartic_factor hc.1 hc.2 c
  · have hh : |residualLinear z (continuedU z) (continuedAtom z)|<
        residualConstant z (continuedU z) (continuedAtom z) := hp.residual
    linarith

/-- The physical closed P₁ exponent domain. -/
def exponentArc : Set ℝ := {t | GW≤Real.cosh t}

def boundaryDerivative (z t : ℝ) : ℝ :=
  continuedUDerivative z*(-Real.sinh t/(Real.cosh t)^2)/Real.sqrt (1+(continuedU z)^2)

/-- The derivative at the switch is explicitly taken within the closed source arc. -/
theorem hasDerivWithinAt_V {z t : ℝ} (hz : z∈Ioc (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) :
    HasDerivWithinAt V (boundaryDerivative z t) exponentArc t := by
  have hzm : z∈Ioo (0 : ℝ) (733/1000) := ⟨hz.1,hz.2.trans_lt zW_bounds.2⟩
  have hzeq : (Real.cosh t)⁻¹=z := by rw [ht]; simp
  have hu : HasDerivAt continuedU (continuedUDerivative z) (Real.cosh t)⁻¹ := by
    rw [hzeq]
    exact continuedU_hasDerivAt hzm
  have hd:=hasDerivAt_boundary_of_source hu
  rw [hzeq] at hd
  apply hd.hasDerivWithinAt.congr_of_mem ?_ ?_
  · intro r hr
    have hz' : 1/Real.cosh r∈Ioc (0 : ℝ) zW :=
      ⟨one_div_pos.mpr (Real.cosh_pos r),
        one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hr⟩
    simpa only [one_div,continuedU] using continuation_optimal hz' (by simp)
  · change GW≤Real.cosh t
    rw [ht]
    have hh:=one_div_le_one_div_of_le hz.1 hz.2
    simpa only [zW,one_div_one_div] using hh

/-- The strict derivative bound includes the physical switch, with the exact
one-sided source-arc meaning made explicit by hasDerivWithinAt_V. -/
theorem abs_boundaryDerivative_lt_one {z t : ℝ} (hz : z∈Ioc (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) : |boundaryDerivative z t|<1 := by
  have hzm : z∈Ioo (0 : ℝ) (733/1000) := ⟨hz.1,hz.2.trans_lt zW_bounds.2⟩
  have hzeq : (Real.cosh t)⁻¹=z := by rw [ht]; simp
  have hu : HasDerivAt continuedU (continuedUDerivative z) (Real.cosh t)⁻¹ := by
    rw [hzeq]
    exact continuedU_hasDerivAt hzm
  have hs : (continuedUDerivative z)^2*((Real.cosh t)⁻¹)^2*(1-((Real.cosh t)⁻¹)^2)<
      1+(continuedU (Real.cosh t)⁻¹)^2 := by
    rw [hzeq]
    exact (continuedU_derivative_bounds hzm).2
  have hh:=abs_deriv_boundary_lt_one (V:=fun r => Real.arsinh (continuedU (Real.cosh r)⁻¹))
    hu Filter.EventuallyEq.rfl hs
  rw [(hasDerivAt_boundary_of_source hu).deriv,hzeq] at hh
  exact hh

/-- The continued source is analytic at every positive point of the full checked domain. -/
theorem continuedU_analyticAt {z : ℝ} (hz : z∈Ioo (0 : ℝ) (733/1000)) :
    AnalyticAt ℝ continuedU z := by
  have hg:=continuation_analyticAt hz
  have hA : AnalyticAt ℝ (fun r => continuation r 0) z :=
    (ContinuousLinearMap.proj (0 : Fin 2) : Coordinates →L[ℝ] ℝ).analyticAt (continuation z) |>.comp hg
  unfold continuedU branchU
  fun_prop

/-- The actual spectral boundary is analytic in the open P₁ regime. -/
theorem V_analyticAt {z t : ℝ} (hz : z∈Ioo (0 : ℝ) zW) (ht : Real.cosh t=1/z) :
    AnalyticAt ℝ V t := by
  have hzm : z∈Ioo (0 : ℝ) (733/1000) := ⟨hz.1,hz.2.trans zW_bounds.2⟩
  have hzeq : (Real.cosh t)⁻¹=z := by rw [ht]; simp
  have hzAna : AnalyticAt ℝ (fun r => (Real.cosh r)⁻¹) t :=
    ((Real.contDiff_cosh : ContDiff ℝ ω Real.cosh).contDiffAt.analyticAt).inv (Real.cosh_pos t).ne'
  have hu : AnalyticAt ℝ (fun r => continuedU (Real.cosh r)⁻¹) t :=
    (continuedU_analyticAt hzm).comp_of_eq hzAna hzeq
  have hc : AnalyticAt ℝ (fun r => Real.arsinh (continuedU (Real.cosh r)⁻¹)) t :=
    Real.analyticAt_arsinh.comp hu
  have hG : GW<Real.cosh t := by
    rw [ht]
    have hh:=one_div_lt_one_div_of_lt hz.1 hz.2
    simpa only [zW,one_div_one_div] using hh
  have hn : ∀ᶠ r in 𝓝 t,GW<Real.cosh r :=
    Real.continuous_cosh.continuousAt.eventually (lt_mem_nhds hG)
  apply hc.congr
  filter_upwards [hn] with r hr
  have hz' : 1/Real.cosh r∈Ioc (0 : ℝ) zW :=
    ⟨one_div_pos.mpr (Real.cosh_pos r),
      one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hr.le⟩
  have hh : V r=Real.arsinh (continuedU (Real.cosh r)⁻¹) := by
    simpa only [one_div,continuedU] using continuation_optimal hz' (by simp)
  exact hh.symm

end polyak.Boundary.P1
