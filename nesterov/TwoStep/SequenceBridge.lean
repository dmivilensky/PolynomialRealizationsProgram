import nesterov.TwoStep.AsymptoticsPhysical
import Mathlib.Topology.Sequences

/-! Exact embedding of physical parameter sequences into real parameter germs.
The background step has a square-root stability margin, so limiting boundary
data require no additional strict-margin hypothesis. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

private theorem positive_decreasing_subsequence {e : ℕ→ℝ}
    (he : Tendsto e atTop (𝓝[>] (0:ℝ))) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ (∀ n,0<e (φ n)) ∧ StrictAnti (e ∘ φ) := by
  have hp : ∀ᶠ n in atTop,0<e n := he.eventually self_mem_nhdsWithin
  obtain ⟨n₀,hn₀⟩ := hp.exists
  have hex (i : {n : ℕ // 0<e n}) : ∃ j : ℕ,i.val<j ∧ 0<e j ∧ e j<e i.val := by
    exact ((eventually_gt_atTop i.val).and (hp.and
      ((he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds i.property)))).exists
  let next (i : {n : ℕ // 0<e n}) : {n : ℕ // 0<e n} :=
    ⟨Classical.choose (hex i),(Classical.choose_spec (hex i)).2.1⟩
  let u : ℕ→{n : ℕ // 0<e n} := fun n=>Nat.rec ⟨n₀,hn₀⟩ (fun _ i=>next i) n
  let φ : ℕ→ℕ := fun n=>(u n).val
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ (by
    intro n
    exact (Classical.choose_spec (hex (u n))).1)
  have ha : StrictAnti (e ∘ φ) := strictAnti_nat_of_succ_lt (by
    intro n
    exact (Classical.choose_spec (hex (u n))).2.2)
  exact ⟨φ,hφ,fun n=>(u n).property,ha⟩

def sequencePatch {B : Type*} (e : ℕ→ℝ) (sample : ℕ→B) (base : ℝ→B) (x : ℝ) : B := by
  classical
  exact if h : ∃ n : ℕ,e n=x then sample (Classical.choose h) else base x

theorem sequencePatch_at_sample {B : Type*} {e : ℕ→ℝ} (he : Function.Injective e)
    (sample : ℕ→B) (base : ℝ→B) (n : ℕ) :
    sequencePatch e sample base (e n)=sample n := by
  classical
  unfold sequencePatch
  split_ifs with h
  · have hn : Classical.choose h=n := he (Classical.choose_spec h)
    rw [hn]
  · exact False.elim (h ⟨n,rfl⟩)

/-- Every continuous readout has its sample limit after this endpoint extension. -/
theorem sequencePatch_read_tendsto {B C : Type*} [TopologicalSpace C]
    {e : ℕ→ℝ} (he : ∀ n,0<e n) (sample : ℕ→B) (base : ℝ→B)
    (read : ℝ→B→C) {c : C}
    (hsample : Tendsto (fun n=>read (e n) (sample n)) atTop (𝓝 c))
    (hbase : Tendsto (fun x=>read x (base x)) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto (fun x=>read x (sequencePatch e sample base x)) (𝓝[>] (0:ℝ)) (𝓝 c) := by
  classical
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsample.eventually hU)
  let bad : Finset ℝ := (Finset.range N).image e
  have hzero : (0:ℝ)∉bad := by
    intro hh
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh
    exact (he i).ne' hi
  have hexclude₀ : ∀ᶠ x in 𝓝 (0:ℝ),x∉bad := bad.finite_toSet.isClosed.isOpen_compl.mem_nhds hzero
  have hexclude : ∀ᶠ x in 𝓝[>] (0:ℝ),x∉bad := hexclude₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hbase.eventually hU,hexclude] with x hx hbad
  change read x (sequencePatch e sample base x)∈U
  unfold sequencePatch
  split_ifs with h
  · let n : ℕ := Classical.choose h
    have hn : N≤n := by
      by_contra hh
      apply hbad
      exact Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr (lt_of_not_ge hh),Classical.choose_spec h⟩
    have hh := hN n hn
    rwa [Classical.choose_spec h] at hh
  · exact hx

namespace Scaling
variable {θ y τ : ℝ} (F : Scaling ℕ atTop θ y τ)

private def bridgeBase (_F : Scaling ℕ atTop θ y τ) (x : ℝ) : Momentum.Tuning :=
  physicalTuning (1-θ*x) τ (y-Real.sqrt x)

private theorem bridgeBase_parameters : ∀ᶠ x in 𝓝[>] (0:ℝ),
    (F.bridgeBase x).beta=1-θ*x ∧ (F.bridgeBase x).tau=τ ∧
      (F.bridgeBase x).stepSize=y-Real.sqrt x := by
  have hx : Tendsto (fun x : ℝ=>x) (𝓝[>] (0:ℝ)) (𝓝 0) := continuous_id.continuousWithinAt.tendsto
  have ht : Tendsto (fun x : ℝ=>θ*x) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa only [mul_zero] using hx.const_mul θ
  have hs : Tendsto (fun x : ℝ=>Real.sqrt x) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa only [Real.sqrt_zero] using hx.sqrt
  filter_upwards [self_mem_nhdsWithin,ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hs.eventually (eventually_lt_nhds F.step_pos)] with x hxp htx hsx
  change 0<x at hxp
  exact physicalTuning_parameters ⟨by linarith,by nlinarith [F.theta_pos],F.tau_nonneg,by linarith⟩

private theorem bridgeBase_stable (hmargin : y*(1+2*τ)≤4) :
    ∀ᶠ x in 𝓝[>] (0:ℝ),(F.bridgeBase x).Stable (x^2) 1 := by
  have hx : Tendsto (fun x : ℝ=>x) (𝓝[>] (0:ℝ)) (𝓝 0) := continuous_id.continuousWithinAt.tendsto
  have hs : Tendsto (fun x : ℝ=>Real.sqrt x) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa only [Real.sqrt_zero] using hx.sqrt
  have hthreshold : 0<(1+2*τ)/(2*θ) := div_pos (by linarith [F.tau_nonneg]) (by linarith [F.theta_pos])
  filter_upwards [F.bridgeBase_parameters,self_mem_nhdsWithin,
    hx.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hs.eventually (eventually_lt_nhds hthreshold)] with x hp hxp hx1 hbound
  change 0<x at hxp
  have hμ : 0<x^2 := sq_pos_of_pos hxp
  have hμL : x^2<1 := by nlinarith
  apply ((F.bridgeBase x).stable_iff hμ hμL).mpr
  rw [hp.1,hp.2.1,hp.2.2]
  have hprod : 2*θ*x<(1+2*τ)*Real.sqrt x := by
    have hh := (lt_div_iff₀ (show 0<2*θ by linarith [F.theta_pos])).mp hbound
    have hm := mul_lt_mul_of_pos_right hh (Real.sqrt_pos.mpr hxp)
    have hsq := Real.sq_sqrt hxp.le
    have heq : 2*θ*(Real.sqrt x)^2=2*θ*x := by rw [hsq]
    nlinarith
  nlinarith

/-- Every stable accelerated sequence has a real-indexed extension agreeing
exactly along a subsequence. All original endpoint hypotheses are retained. -/
theorem exists_real_extension
    (hstable : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1)
    (hmargin : y*(1+2*τ)≤4) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ G : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ,
      G.epsilon=id ∧ (∀ n,G.tuning (F.epsilon (φ n))=F.tuning (φ n)) ∧
      ∀ᶠ x in 𝓝[>] (0:ℝ),(G.tuning x).Stable (x^2) 1 := by
  classical
  obtain ⟨φ,hφ,hepos,heanti⟩ := positive_decreasing_subsequence F.epsilon_tendsto
  let e : ℕ→ℝ := F.epsilon ∘ φ
  let q : ℕ→Momentum.Tuning := F.tuning ∘ φ
  let g : ℝ→Momentum.Tuning := sequencePatch e q F.bridgeBase
  have he : Function.Injective e := heanti.injective
  have hx : Tendsto (fun x : ℝ=>x) (𝓝[>] (0:ℝ)) (𝓝 0) := continuous_id.continuousWithinAt.tendsto
  have hbθ : Tendsto (fun x=>(1-(F.bridgeBase x).beta)/x) (𝓝[>] (0:ℝ)) (𝓝 θ) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [F.bridgeBase_parameters,self_mem_nhdsWithin] with x hp hxp
    change 0<x at hxp
    rw [hp.1]
    field_simp [hxp.ne']
    ring
  have hby : Tendsto (fun x=>(F.bridgeBase x).stepSize) (𝓝[>] (0:ℝ)) (𝓝 y) := by
    have ht := (tendsto_const_nhds (x:=y)).sub hx.sqrt
    simp only [Real.sqrt_zero,sub_zero] at ht
    apply ht.congr'
    filter_upwards [F.bridgeBase_parameters] with x hp
    exact hp.2.2.symm
  have hbt : Tendsto (fun x=>(F.bridgeBase x).tau) (𝓝[>] (0:ℝ)) (𝓝 τ) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [F.bridgeBase_parameters] with x hp
    exact hp.2.1.symm
  have hθ := sequencePatch_read_tendsto hepos q F.bridgeBase (fun x p=>(1-p.beta)/x)
    (F.theta_tendsto.comp hφ.tendsto_atTop) hbθ
  have hy := sequencePatch_read_tendsto hepos q F.bridgeBase (fun _ p=>p.stepSize)
    (F.step_tendsto.comp hφ.tendsto_atTop) hby
  have ht := sequencePatch_read_tendsto hepos q F.bridgeBase (fun _ p=>p.tau)
    (F.tau_tendsto.comp hφ.tendsto_atTop) hbt
  let G : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ := {
    epsilon := id
    tuning := g
    epsilon_tendsto := tendsto_id
    theta_tendsto := hθ
    step_tendsto := hy
    tau_tendsto := ht
    theta_pos := F.theta_pos
    step_pos := F.step_pos
    tau_nonneg := F.tau_nonneg }
  refine ⟨φ,hφ,G,rfl,fun n=>sequencePatch_at_sample he q F.bridgeBase n,?_⟩
  have hqstable : ∀ᶠ n in atTop,(q n).Stable (e n^2) 1 := hφ.tendsto_atTop.eventually hstable
  have hsq : Tendsto (fun n=>if (q n).Stable (e n^2) 1 then (1:ℝ) else 0) atTop (𝓝 1) := by
    apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
    filter_upwards [hqstable] with n hn
    exact (ite_eq_left hn).symm
  have hsb : Tendsto (fun x : ℝ=>if (F.bridgeBase x).Stable (x^2) 1 then (1:ℝ) else 0)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
    filter_upwards [F.bridgeBase_stable hmargin] with x hx
    exact (ite_eq_left hx).symm
  have hread := sequencePatch_read_tendsto hepos q F.bridgeBase
    (fun (x : ℝ) (p : Momentum.Tuning)=>if p.Stable (x^2) 1 then (1:ℝ) else 0)
    hsq hsb
  have hev := hread.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hev] with x hx
  change 0<(if (g x).Stable (x^2) 1 then (1:ℝ) else 0) at hx
  split_ifs at hx with h
  · exact h
  · exact False.elim (lt_irrefl (0:ℝ) hx)

end Scaling
end
end nesterov.TwoStep
