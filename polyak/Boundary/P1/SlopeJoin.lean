import polyak.Boundary.P1.Results
import polyak.Boundary.Envelope
import polyak.Boundary.SpiralRegularity

/-! The actual P1/spiral boundary is differentiable at the outer switch.
A differentiated contact equation identifies the exact source slope. -/
noncomputable section
namespace polyak.Boundary.P1
open Spectral Envelope Filter
open scoped Topology

private def contact (v : Point) : ℝ := quartic (v 1) (v 0) (v 2)
private def base : Point := point (1-zW/2) zW (-zW/2)
private def L : Point →L[ℝ] ℝ := fderiv ℝ contact base

private theorem contact_differentiable (v : Point) : DifferentiableAt ℝ contact v := by
  unfold contact quartic
  fun_prop

private theorem contact_c_zero : L (basis 2)=0 := by
  have hd:=(contact_differentiable base).hasFDerivAt.comp_hasDerivAt (-zW/2)
    (point_hasDerivAt (hasDerivAt_const (-zW/2) (1-zW/2))
      (hasDerivAt_const (-zW/2) zW) (hasDerivAt_id (-zW/2)))
  have hb : point (0 : ℝ) 0 1=basis 2 := by ext i; fin_cases i <;> simp [point,basis]
  rw [hb] at hd
  exact (hd.unique (quartic_hasDerivAt zW (1-zW/2) (-zW/2))).trans endpoint_contacts.2

private theorem contact_u_pos : 0<L (basis 0) := by
  let u:=1-zW/2
  let c:= -zW/2
  have hd:=(contact_differentiable base).hasFDerivAt.comp_hasDerivAt u
    (point_hasDerivAt (hasDerivAt_id u) (hasDerivAt_const u zW) (hasDerivAt_const u c))
  have hb : point (1 : ℝ) 0 0=basis 0 := by ext i; fin_cases i <;> simp [point,basis]
  rw [hb] at hd
  have he : HasDerivAt (fun r => quartic zW r c)
      (2*u*(2+zW*c+zW^2*(c^2-1))+2*zW*(1-c^2)*(1+zW*c)) u := by
    have hg:=((hasDerivAt_const u (1-c^2)).sub ((hasDerivAt_id u).pow 2)).mul_const
      (2+zW*c+zW^2*(c^2-1))
    have hh:=((hasDerivAt_id u).const_mul (2*zW)).mul_const ((1-c^2)*(1+zW*c))
    convert hg.neg.add hh using 1
    · funext r
      dsimp [quartic]
      ring
    · dsimp only [id_eq]
      ring
  have heq : L (basis 0)=2*u*(2+zW*c+zW^2*(c^2-1))+2*zW*(1-c^2)*(1+zW*c) := hd.unique he
  rw [heq]
  have hu : 0<u := by dsimp [u]; linarith [zW_bounds.2]
  have hz2 : zW^2<1 := by nlinarith [zW_pos,zW_bounds.2]
  have hc2 : c^2<1 := by dsimp [c]; nlinarith
  have hzc : 0<1+zW*c := by dsimp [c]; nlinarith
  have halpha : 0<2+zW*c+zW^2*(c^2-1) := by
    dsimp [c]
    nlinarith [sq_nonneg (zW^2)]
  exact add_pos (mul_pos (mul_pos (by norm_num) hu) halpha)
    (mul_pos (mul_pos (mul_pos (by norm_num) zW_pos) (by linarith)) hzc)

private theorem endpoint_values : continuedU zW=1-zW/2 ∧ continuedAtom zW= -zW/2 := by
  unfold continuedU continuedAtom
  rw [continuation_endpoint,endpoint_u,endpoint_atom]
  exact ⟨rfl,rfl⟩

/-- The source slope agrees exactly with the spiral at the outer join. -/
theorem continuedUDerivative_zW : continuedUDerivative zW= -1/2 := by
  have hz : zW∈Set.Ioo (0 : ℝ) (733/1000) := ⟨zW_pos,zW_bounds.2⟩
  have hb:=(ContinuousLinearMap.proj (1 : Fin 2) : Coordinates →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt zW
    (continuation_analyticAt hz).differentiableAt.hasDerivAt
  have hx:=((hasDerivAt_id zW).pow 2).mul hb
  have hsource:=contact_hasDerivAt (D:=contact) (u:=continuedU) (G:=fun r : ℝ => r)
    (c:=continuedAtom) (contact_differentiable _) (continuedU_hasDerivAt hz) (hasDerivAt_id zW) hx
    (by rw [endpoint_values.1,endpoint_values.2]; exact contact_c_zero)
  have hzero : (fun r => contact (point (continuedU r) r (continuedAtom r))) =ᶠ[𝓝 zW] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with r hr
    exact (regularSystem_contacts (continuation_source ⟨hr.1.le,hr.2.le⟩)).1
  have he1:=hsource.unique ((hasDerivAt_const zW (0 : ℝ)).congr_of_eventuallyEq hzero)
  rw [endpoint_values.1,endpoint_values.2] at he1
  have hspiral:=contact_hasDerivAt (D:=contact) (u:=fun r : ℝ => 1-r/2)
    (G:=fun r : ℝ => r) (c:=fun r : ℝ => -r/2) (contact_differentiable base)
    ((hasDerivAt_const zW (1 : ℝ)).sub ((hasDerivAt_id zW).div_const 2))
    (hasDerivAt_id zW) ((hasDerivAt_id zW).neg.div_const 2) contact_c_zero
  have hzero2 : (fun r : ℝ => contact (point (1-r/2) r (-r/2)))=fun _ => 0 := by
    funext r
    unfold contact point quartic
    dsimp
    ring
  rw [hzero2] at hspiral
  have he2:=hspiral.unique (hasDerivAt_const zW (0 : ℝ))
  have he : L (basis 0)*(continuedUDerivative zW+1/2)=0 := by
    dsimp only [L,base]
    linear_combination he1-he2
  have hs:=(mul_eq_zero.mp he).resolve_left contact_u_pos.ne'
  linarith

/-- The derivative formulas of the two actual source arcs agree at GW. -/
theorem boundaryDerivative_at_GW {t : ℝ} (ht : Real.cosh t=GW) :
    boundaryDerivative zW t=Boundary.spiralBoundaryDerivative t := by
  unfold boundaryDerivative Boundary.spiralBoundaryDerivative
  rw [continuedUDerivative_zW,endpoint_values.1,ht]
  unfold zW
  ring

/-- Ordinary differentiability at both copies of the outer switch. -/
theorem hasDerivAt_V_at_GW {t : ℝ} (ht : Real.cosh t=GW) :
    HasDerivAt V (boundaryDerivative zW t) t := by
  have hp:=hasDerivWithinAt_V ⟨zW_pos,le_rfl⟩
    (ht.trans (by unfold zW; simp))
  have hs:=Boundary.hasDerivWithinAt_V_spiral
    (show t∈Boundary.spiralExponentArc from ⟨by rw [ht]; exact G1_lt_GW.le,ht.le⟩)
  rw [←boundaryDerivative_at_GW ht] at hs
  apply (hp.union hs).hasDerivAt
  have hn : {s : ℝ | G1<Real.cosh s}∈𝓝 t :=
    (isOpen_lt continuous_const Real.continuous_cosh).mem_nhds
      (by change G1<Real.cosh t; rw [ht]; exact G1_lt_GW)
  apply Filter.mem_of_superset hn
  intro s hs
  by_cases h : GW≤Real.cosh s
  · exact Or.inl h
  · exact Or.inr ⟨hs.le,le_of_not_ge h⟩

theorem abs_deriv_V_at_GW_lt_one {t : ℝ} (ht : Real.cosh t=GW) : |deriv V t|<1 := by
  rw [(hasDerivAt_V_at_GW ht).deriv]
  exact abs_boundaryDerivative_lt_one ⟨zW_pos,le_rfl⟩ (ht.trans (by unfold zW; simp))

end polyak.Boundary.P1
