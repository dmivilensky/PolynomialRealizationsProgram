import jacobi.Bessel.Zeros
import jacobi.Analytic.BesselComposition
import jacobi.Analytic.BesselDerivativeContinuity
import jacobi.Analysis.HolomorphicZeroDisk

/-!
Article: jacobi, Lemma E.1.
Use: the finitely many initial numbered zeros can be continued on one common smaller order disk and combined with the original uniform infinite tail.
-/
namespace jacobi.Bessel
noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every genuine Bessel spectral zero has an actual locally unique holomorphic order continuation, centered at exactly the original zero.
Use: the finitely many initial numbered zeros can be continued on one common smaller order disk and combined with the original uniform infinite tail.
Article: jacobi, Lemma E.1.
Proof: normalize the original function by its actual nonzero spectral derivative at the zero. Joint continuity of the genuine derivative gives a true uniform half-contraction on a product neighborhood; actual order continuity bounds the original center residual. Apply the proved holomorphic zero-disk theorem, discharging its composition hypothesis by the original Bessel coefficient series. -/
theorem normalized_local_holomorphic_zero {a0 z0 : ℂ} (ha0 : -1<a0.re)
    (hz0 : normalized a0 z0=0) :
    ∃ r s : ℝ,∃ v : ℂ → ℂ,0<r ∧ 0<s ∧ DifferentiableOn ℂ v (ball a0 r) ∧ v a0=z0 ∧
      ∀ a : ℂ,‖a-a0‖<r → -1<a.re ∧ ‖v a-z0‖≤s ∧ normalized a (v a)=0 ∧
        ∀ z : ℂ,‖z-z0‖≤s → normalized a z=0 → z=v a := by
  -- The true derivative is nonzero by original Bessel simplicity, not an implicit-function premise.
  let d : ℂ := deriv (normalized a0) z0
  have hd : d≠0 := normalized_zero_simple ha0 hz0
  let f (a ζ : ℂ) : ℂ := normalized a (z0+ζ)/d
  let f' (a ζ : ℂ) : ℂ := deriv (normalized a) (z0+ζ)/d
  have hU : IsOpen {p : ℂ × ℂ | -1<p.1.re} := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have hder : ContinuousAt (fun p : ℂ × ℂ => 1-f' p.1 p.2) (a0,0) := by
    have hraw : ContinuousAt (fun p : ℂ × ℂ => deriv (normalized p.1) p.2) (a0,z0) :=
      normalized_slope_joint_continuous.continuousAt
        (hU.mem_nhds (show (a0,z0)∈{p : ℂ × ℂ | -1<p.1.re} from ha0))
    have hmap : ContinuousAt (fun p : ℂ × ℂ => (p.1,z0+p.2)) (a0,0) := by fun_prop
    have hcont : ContinuousAt (fun p : ℂ × ℂ => deriv (normalized p.1) (z0+p.2)) (a0,0) := by
      exact hraw.comp_of_eq hmap (by simp)
    exact continuousAt_const.sub (hcont.div_const d)
  have hbase : 1-f' a0 0=0 := by change 1-deriv (normalized a0) (z0+0)/d=0; rw [add_zero,div_self hd,sub_self]
  have hnearder : ∀ᶠ p : ℂ × ℂ in 𝓝 (a0,0),‖1-f' p.1 p.2‖<1/2 :=
    hder.norm.eventually_lt_const (by change ‖1-f' a0 0‖<1/2; rw [hbase]; norm_num)
  obtain ⟨ε,hε,hεbound⟩ := Metric.mem_nhds_iff.mp hnearder
  let s : ℝ := ε/2
  have hs : 0<s := half_pos hε
  have hcenter : ContinuousAt (fun a : ℂ => f a 0) a0 := by
    have hh := (normalized_order_holomorphic z0).continuousOn.continuousAt (order_halfPlane_open.mem_nhds ha0)
    simpa only [f,add_zero] using hh.div_const d
  have hbase0 : f a0 0=0 := by simp only [f,add_zero,hz0,zero_div]
  have hnearcenter : ∀ᶠ a in 𝓝 a0,‖f a 0‖<s/2 := hcenter.norm.eventually_lt_const (by change ‖f a0 0‖<s/2; rw [hbase0,norm_zero]; exact half_pos hs)
  obtain ⟨r,hr,hrbound⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ a in 𝓝 a0,-1<a.re from order_halfPlane_open.mem_nhds ha0).and (hnearcenter.and (Metric.ball_mem_nhds a0 (half_pos hε))))
  have hdata (a : ℂ) (ha : a∈ball a0 r) : -1<a.re ∧ ‖f a 0‖≤s/2 ∧ dist a a0<ε/2 := by
    obtain ⟨hreal,hc,hδ⟩ := hrbound ha
    exact ⟨hreal,hc.le,hδ⟩
  have hderiv (a : ℂ) (_ha : a∈ball a0 r) (ζ : ℂ) (_hζ : ζ∈closedBall (0:ℂ) s) :
      HasDerivAt (f a) (f' a ζ) ζ := by
    convert! (((normalized_analytic a (z0+ζ)).differentiableAt.hasDerivAt).comp ζ
      ((hasDerivAt_id ζ).const_add z0)).div_const d using 1
    simp only [f',mul_one]
  have hbound (a : ℂ) (ha : a∈ball a0 r) (ζ : ℂ) (hζ : ζ∈closedBall (0:ℂ) s) :
      ‖1-f' a ζ‖≤1/2 := by
    have hζ' : ‖ζ‖≤ε/2 := by simpa only [s,mem_closedBall,dist_zero_right] using hζ
    have hp : (a,ζ)∈ball (a0,0) ε := by
      rw [mem_ball,Prod.dist_eq,dist_zero_right]
      exact max_lt ((hdata a ha).2.2.trans (half_lt_self hε)) (hζ'.trans_lt (half_lt_self hε))
    have hh := @hεbound (a,ζ) hp
    change ‖1-f' a ζ‖<1/2 at hh
    exact hh.le
  have hcomp (v : ℂ → ℂ) (hv : DifferentiableOn ℂ v (ball a0 r)) (_hvbound : ∀ a∈ball a0 r,‖v a‖≤s) :
      DifferentiableOn ℂ (fun a => f a (v a)) (ball a0 r) := by
    intro a ha
    have hvA := hv.analyticOnNhd isOpen_ball a ha
    have hzA : AnalyticAt ℂ (fun b => z0+v b) a := analyticAt_const.add hvA
    exact ((normalized_comp_analytic analyticAt_id hzA (hdata a ha).1).div_const
      (c := d)).differentiableAt.differentiableWithinAt
  obtain ⟨u,hu,hroot⟩ := jacobi.Analysis.holomorphic_unique_zero_disk isOpen_ball hs.le
    hderiv hbound (fun a ha => (hdata a ha).2.1) hcomp
  have hcenterMem : a0∈ball a0 r := mem_ball_self hr
  have hu0 : u a0=0 := ((hroot a0 hcenterMem).2.2.2 0 (by simpa using hs.le) hbase0).symm
  refine ⟨r,s,(fun a => z0+u a),hr,hs,differentiableOn_const z0 |>.add hu,by simp only [hu0,add_zero],fun a ha => ?_⟩
  have ha' : a∈ball a0 r := by simpa only [mem_ball,dist_eq_norm] using ha
  obtain ⟨hsize,hzero,_hsimple,hunique⟩ := hroot a ha'
  have hztrue : normalized a (z0+u a)=0 := by simpa only [f,div_eq_zero_iff,hd,or_false] using hzero
  refine ⟨(hdata a ha').1,by simpa only [add_sub_cancel_left] using hsize,hztrue,fun z hz he => ?_⟩
  have hzdisk : ‖z-z0‖≤s := hz
  have hfzero : f a (z-z0)=0 := by
    have harg : z0+(z-z0)=z := by ring
    change normalized a (z0+(z-z0))/d=0
    rw [harg,he,zero_div]
  have hh := hunique (z-z0) hzdisk hfzero
  linear_combination hh

end
end jacobi.Bessel
