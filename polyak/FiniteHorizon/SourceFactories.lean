import polyak.FiniteHorizon.LinearGap
import polyak.Boundary.P1.Results
import polyak.Boundary.P2.Results
import polyak.Boundary.P5.LocalOptimal

/-!
Article: Appendix C, source factories along the actual boundary.
Use: the true P₁, P₂, spiral and central P₅ formulas supply factors for every
admissible positive correction, with the physical multiplier and exact values.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Filter Set
open scoped Topology

def HasPhysicalFactors7 (q t : ℝ) : Prop :=
  ∃ W : DualWeights,(∀ n∈W.lags,n≤5) ∧ ∀ (γ ε : ℝ) (hγ : 0≤γ),
    Real.sinh (V t)≤Real.sinh (t-Real.log q) →
    4*γ≤Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2 →
    ε≤(Real.cosh t-1)*(Real.sinh (t-Real.log q)^2-Real.sinh (V t)^2)+
      2*γ*Real.sinh (t-Real.log q)^2 →
    Nonempty (BandedData7 (normalizedMatrix7 W q t γ hγ) (normalizedValues7 W t γ hγ) ε)

theorem hasPhysicalFactors7_p2 {q t : ℝ} (hq : 0<q)
    (ht : Real.cosh t∈Icc P2.Ga G1) : HasPhysicalFactors7 q t := by
  obtain ⟨z,hz,_⟩:=P2.p2_arc ht
  have hzm:=P2.arc_mem_interval hz.1
  refine ⟨P2.dualWeights z hzm,p2_weights_lag_le_five hzm,?_⟩
  intro γ ε hγ huv hs hε
  have hu : Real.sinh (V t)=P2.u z:=by rw [hz.2.2,Real.sinh_arsinh]
  rw [hu] at huv hs hε
  rw [hz.2.1] at hε
  exact ⟨p2PhysicalBandedData7 hzm hq hz.2.1 hγ huv hs hε⟩

theorem hasPhysicalFactors7_spiral {q t : ℝ} (hq : 0<q)
    (hG : G1≤Real.cosh t) (hGW : Real.cosh t≤GW) : HasPhysicalFactors7 q t := by
  let W:=weights23 (spiralWeight (Real.cosh t)) (spiralWeight_mem (Real.one_le_cosh t) hGW).1
    (spiralWeight_mem (Real.one_le_cosh t) hGW).2
  refine ⟨W,spiral_weights_lag_le_five (Real.one_le_cosh t) hGW,?_⟩
  intro γ ε hγ huv hs hε
  have hu : Real.sinh (V t)=1-1/(2*Real.cosh t):=by rw [spiral_optimal hG hGW,Real.sinh_arsinh]
  rw [hu] at huv hs hε
  exact ⟨spiralPhysicalBandedData7 hq hG hGW hγ huv hs hε⟩

theorem hasPhysicalFactors7_oneAtom {q t : ℝ} (hq : 0<q) (ht : GW≤Real.cosh t) :
    HasPhysicalFactors7 q t := by
  let z:=1/Real.cosh t
  have hz : z∈Ioc (0 : ℝ) P1.zW:=
    ⟨one_div_pos.mpr (Real.cosh_pos _),one_div_le_one_div_of_le (by linarith [GW_bounds.1]) ht⟩
  have hz1 : z≤1:=by dsimp [z]; exact (div_le_one (Real.cosh_pos t)).mpr (Real.one_le_cosh t)
  have he : Real.cosh t=1/z:=by simp [z]
  have hp:=P1.continuation_physical hz
  have hc:=P1.regularSystem_contacts (P1.continuation_source ⟨hz.1.le,hz.2.trans P1.zW_bounds.2.le⟩)
  have hu : Real.sinh (V t)=P1.continuedU z:=by
    rw [P1.continuation_optimal hz he,Real.sinh_arsinh]
    rfl
  refine ⟨P1.weights,oneAtom_weights_lag_le_five,?_⟩
  intro γ ε hγ huv hs hε
  rw [hu] at huv hs hε
  rw [he] at hε
  have hnonneg : 0≤P1.continuedU z:=by linarith [(P1.continuedU_bounds hz).1]
  exact ⟨oneAtomPhysicalBandedData7 (u:=P1.continuedU z) hz.1 hz1 hc.1 hc.2 hp.residual.le hq he
    hnonneg hγ huv hs hε⟩

theorem hasPhysicalFactors7_of_cosh_ge_Ga {q t : ℝ} (hq : 0<q) (ht : P2.Ga≤Real.cosh t) :
    HasPhysicalFactors7 q t := by
  by_cases hG : Real.cosh t≤G1
  · exact hasPhysicalFactors7_p2 hq ⟨ht,hG⟩
  · by_cases hGW : Real.cosh t≤GW
    · exact hasPhysicalFactors7_spiral hq (lt_of_not_ge hG).le hGW
    · exact hasPhysicalFactors7_oneAtom hq (lt_of_not_ge hGW).le

theorem eventually_hasPhysicalFactors7_of_cosh_gt_Ga {q T : ℝ} (hq : 0<q) (ht : P2.Ga<Real.cosh T) :
    ∀ᶠ t in 𝓝 T,HasPhysicalFactors7 q t := by
  filter_upwards [Real.continuous_cosh.continuousAt.eventually (lt_mem_nhds ht)] with t hG
  exact hasPhysicalFactors7_of_cosh_ge_Ga hq hG.le

theorem eventually_hasPhysicalFactors7_p5 {q : ℝ} (hq : 0<q) :
    ∀ᶠ t in 𝓝 (0 : ℝ),HasPhysicalFactors7 q t := by
  obtain ⟨hstar,hstarpos,_,_,hopt⟩:=P5.central_family_local
  have hfun : Tendsto (fun t : ℝ => Real.cosh t-1) (𝓝 0) (𝓝 0):=by
    have hc : Continuous (fun t : ℝ => Real.cosh t-1):=by fun_prop
    simpa only [Real.cosh_zero,sub_self] using hc.tendsto (0 : ℝ)
  have hf:=hfun.eventually eventually_p5PhysicalBandedData7
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ),Real.cosh t<1+hstar:=
    Real.continuous_cosh.continuousAt.eventually (gt_mem_nhds (by simpa using hstarpos))
  filter_upwards [hf,hg] with t ht hG
  have hh : 0≤Real.cosh t-1:=by linarith [Real.one_le_cosh t]
  obtain ⟨h₂,h₃,h₅,hdata⟩:=ht hh
  let W:=P5.weights235 (P5.localBranch (Real.cosh t-1) 5) (P5.localBranch (Real.cosh t-1) 6) h₂ h₃ h₅
  refine ⟨W,p5_weights_lag_le_five h₂ h₃ h₅,?_⟩
  intro γ ε hγ huv hs hε
  have hu : Real.sinh (V t)=1/2+(Real.cosh t-1)*P5.localBranch (Real.cosh t-1) 0:=by
    rw [hopt t hG.le]
    simp only [P5.localValue,Real.sinh_arsinh,P5.branchU]
  rw [hu] at huv hs hε
  have he : Real.cosh t=1+(Real.cosh t-1):=by ring
  have hε' : ε≤(Real.cosh t-1)*
      (Real.sinh (t-Real.log q)^2-(1/2+(Real.cosh t-1)*P5.localBranch (Real.cosh t-1) 0)^2)+
      2*γ*Real.sinh (t-Real.log q)^2:=hε
  exact hdata q t γ ε hq hγ he huv hs hε'

end polyak.FiniteHorizon
