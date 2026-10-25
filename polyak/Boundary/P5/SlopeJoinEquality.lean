import polyak.Boundary.P5.SlopeJoinPairing

/-! The exact KKT envelope slope equality at the P2/P5 endpoint. -/
noncomputable section
namespace polyak.Boundary.P5.SlopeJoin
open Spectral Filter Envelope
open scoped Topology

def coefficient (i : Fin 3) : ℝ :=
  (1-P2.p P2.zetaA)*fderiv ℝ (symbol (P2.W P2.zetaA))
    (point (P2.u P2.zetaA) P2.Ga (P2.x P2.zetaA)) (basis i)+
  P2.p P2.zetaA*fderiv ℝ (symbol (P2.W P2.zetaA))
    (point (P2.u P2.zetaA) P2.Ga (P2.y P2.zetaA)) (basis i)

theorem coefficient_zero_pos : 0<coefficient 0 := by
  have hp:=P2.p_mem P2.zetaA_mem P2.zeta1_lt_zetaA.le
  have hx:=P2.x_bounds P2.zetaA_mem
  have hy:=P2.y_bounds P2.zetaA_mem
  have hu : 0<P2.u P2.zetaA := by linarith [P2.u_lower_positive P2.zetaA P2.zetaA_mem]
  have hdx:=symbol_u_partial_pos hu (P2.one_lt_G P2.zetaA_mem)
    (P2.weight_bounds P2.zetaA_mem) (show -1<P2.x P2.zetaA ∧ P2.x P2.zetaA<1 by constructor <;> linarith)
  have hdy:=symbol_u_partial_pos hu (P2.one_lt_G P2.zetaA_mem)
    (P2.weight_bounds P2.zetaA_mem) (show -1<P2.y P2.zetaA ∧ P2.y P2.zetaA<1 by constructor <;> linarith)
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hdx) (mul_nonneg hp.1 hdy.le)

theorem p2_envelope_equation :
    coefficient 0*(P2.slope P2.zetaA*P2.GDerivative P2.zetaA)+
      coefficient 1*P2.GDerivative P2.zetaA=0 := by
  have hz:=P2.arc_mem_interior ⟨P2.zeta1_lt_zetaA.le,le_rfl⟩
  obtain ⟨hx,hy,hp⟩:=p2_coordinates_differentiable hz
  have hzero : (fun r => (1-P2.p r)*symbol (P2.W P2.zetaA) (point (P2.u r) (P2.G r) (P2.x r))+
      P2.p r*symbol (P2.W P2.zetaA) (point (P2.u r) (P2.G r) (P2.y r))) =ᶠ[𝓝 P2.zetaA] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2,Ioi_mem_nhds P2.zeta1_lt_zetaA] with r hr h1
    exact p2_pairing_zero ⟨hr.1.le,hr.2.le⟩ h1.le (P2.weight_bounds P2.zetaA_mem)
  obtain ⟨hx0,hxc⟩:=symbol_p2_contact P2.zetaA_mem (Or.inl rfl)
  obtain ⟨hy0,hyc⟩:=symbol_p2_contact P2.zetaA_mem (Or.inr rfl)
  exact twoAtom_derivative (P2.hasDerivAt_u P2.zetaA_mem) (P2.hasDerivAt_G P2.zetaA_mem)
    hp.hasDerivAt hx.hasDerivAt hy.hasDerivAt
    (symbol_differentiable _ _) (symbol_differentiable _ _) hx0 hy0 hxc hyc hzero

theorem endpoint_values :
    continuationU (P2.Ga-1)=P2.u P2.zetaA ∧
    branchX (P2.Ga-1) (Selection.continuation (P2.Ga-1))=P2.x P2.zetaA ∧
    (P2.Ga-1)*Selection.continuation (P2.Ga-1) 3=P2.p P2.zetaA ∧
    Selection.continuation (P2.Ga-1) 2=P2.y P2.zetaA := by
  rw [continuationU,continuation_endpoint]
  obtain ⟨hu,hx,hp,_⟩:=p2Lift_coordinates P2.zetaA_mem
  exact ⟨hu,hx,hp,rfl⟩

theorem p5_envelope_equation :
    coefficient 0*(Selection.continuation (P2.Ga-1) 0+
      (P2.Ga-1)*deriv Selection.continuation (P2.Ga-1) 0)+coefficient 1=0 := by
  let h:=P2.Ga-1
  have hmem : h∈Set.Ioo (0 : ℝ) (11791/500000) := ⟨centralEndpoint_pos,centralEndpoint_lt⟩
  have hg:=(Selection.analyticAt hmem).differentiableAt.hasDerivAt
  have hi (i : Fin 7) : HasDerivAt (fun r => Selection.continuation r i)
      (deriv Selection.continuation h i) h :=
    (ContinuousLinearMap.proj i : Coordinates →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hg
  have hp:=((hasDerivAt_id h).mul (hi 3))
  have hx:=((hasDerivAt_id h).mul (hi 1)).const_add (-1/2 : ℝ)
  have hy:=hi 2
  have hzero : (fun r => (1-r*Selection.continuation r 3)*
      symbol (P2.W P2.zetaA) (point (continuationU r) (1+r) (branchX r (Selection.continuation r)))+
      r*Selection.continuation r 3*symbol (P2.W P2.zetaA)
        (point (continuationU r) (1+r) (Selection.continuation r 2))) =ᶠ[𝓝 h] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with r hr
    exact symbol_pairing_zero hr.1.le (Selection.continuation_source ⟨hr.1.le,hr.2.le⟩)
      (P2.weight_bounds P2.zetaA_mem)
  obtain ⟨hu,hxv,hpv,hyv⟩:=endpoint_values
  have hG : 1+h=P2.G P2.zetaA := by dsimp [h,P2.Ga]; ring
  obtain ⟨hx0,hxc⟩:=symbol_p2_contact P2.zetaA_mem (Or.inl rfl)
  obtain ⟨hy0,hyc⟩:=symbol_p2_contact P2.zetaA_mem (Or.inr rfl)
  have hx0' : symbol (P2.W P2.zetaA) (point (continuationU h) (1+h)
      (branchX h (Selection.continuation h)))=0 := by rw [hu,hG,hxv]; exact hx0
  have hy0' : symbol (P2.W P2.zetaA) (point (continuationU h) (1+h)
      (Selection.continuation h 2))=0 := by rw [hu,hG,hyv]; exact hy0
  have hxc' : fderiv ℝ (symbol (P2.W P2.zetaA)) (point (continuationU h) (1+h)
      (branchX h (Selection.continuation h))) (basis 2)=0 := by rw [hu,hG,hxv]; exact hxc
  have hyc' : fderiv ℝ (symbol (P2.W P2.zetaA)) (point (continuationU h) (1+h)
      (Selection.continuation h 2)) (basis 2)=0 := by rw [hu,hG,hyv]; exact hyc
  have he:=twoAtom_derivative (G:=fun r : ℝ => 1+r)
    (p:=fun r : ℝ => r*Selection.continuation r 3)
    (x:=fun r : ℝ => branchX r (Selection.continuation r))
    (continuationU_hasDerivAt hmem) ((hasDerivAt_id h).const_add 1)
    hp hx hy (symbol_differentiable _ _) (symbol_differentiable _ _) hx0' hy0' hxc' hyc' hzero
  rw [hu,hG,hxv,hpv,hyv] at he
  simpa only [coefficient,h,P2.Ga,mul_one] using he

/-- The two independently defined analytic source branches have exactly the same physical slope. -/
theorem source_slope_eq :
    Selection.continuation (P2.Ga-1) 0+(P2.Ga-1)*deriv Selection.continuation (P2.Ga-1) 0=
      P2.slope P2.zetaA := by
  have hg : P2.GDerivative P2.zetaA≠0 := (P2.GDerivative_neg P2.zetaA_mem).ne
  have hp2:=p2_envelope_equation
  have hp5:=p5_envelope_equation
  have hs : coefficient 0*(Selection.continuation (P2.Ga-1) 0+
      (P2.Ga-1)*deriv Selection.continuation (P2.Ga-1) 0-P2.slope P2.zetaA)=0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hg
    linear_combination (P2.GDerivative P2.zetaA)*hp5-hp2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left coefficient_zero_pos.ne')

end polyak.Boundary.P5.SlopeJoin
