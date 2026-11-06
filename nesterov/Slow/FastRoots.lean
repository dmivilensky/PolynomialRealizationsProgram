import nesterov.Slow.Continuity
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Ultrafilter

/-! Upper stability of actual roots under fixed-degree coefficient limits. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set
open scoped Topology NNReal

section Complex
variable {A : Type*} {l : Filter A} {p : A→Polynomial ℂ} {p₀ : Polynomial ℂ} {N : ℕ}

 theorem cauchyBound_tendsto (hdeg : ∀ a,(p a).natDegree=N) (hdeg₀ : p₀.natDegree=N)
    (hp₀ : p₀≠0) (hc : ∀ j,Tendsto (fun a=>(p a).coeff j) l (𝓝 (p₀.coeff j))) :
    Tendsto (fun a=>(p a).cauchyBound) l (𝓝 p₀.cauchyBound) := by
  have hn := Filter.Tendsto.finset_sup_nhds_apply (s:=Finset.range N)
    (fun j _=>(hc j).nnnorm)
  have hd := (hc N).nnnorm
  have hne : ‖p₀.coeff N‖₊≠0 := by
    rw [←hdeg₀,coeff_natDegree]
    simpa using (leadingCoeff_ne_zero.mpr hp₀)
  have hh := (hn.div hd hne).add_const 1
  simpa only [cauchyBound,←coeff_natDegree,hdeg,hdeg₀,Pi.div_apply] using hh

 theorem roots_eventually_bounded (hdeg : ∀ a,(p a).natDegree=N) (hdeg₀ : p₀.natDegree=N)
    (hp₀ : p₀≠0) (hc : ∀ j,Tendsto (fun a=>(p a).coeff j) l (𝓝 (p₀.coeff j))) :
    ∃ R : ℝ,∀ᶠ a in l,∀ z : ℂ,(p a).eval z=0 → ‖z‖≤R := by
  have ht := (NNReal.continuous_coe.tendsto _).comp (cauchyBound_tendsto hdeg hdeg₀ hp₀ hc)
  have hn : p₀.coeff N≠0 := by rw [←hdeg₀,coeff_natDegree];exact leadingCoeff_ne_zero.mpr hp₀
  have hpn := (hc N).eventually_ne hn
  refine ⟨(p₀.cauchyBound:ℝ)+1,?_⟩
  have hb := ht.eventually (eventually_lt_nhds (lt_add_one (p₀.cauchyBound:ℝ)))
  filter_upwards [hb,hpn] with a ha hanz z hz
  have hpa : p a≠0 := by intro hh;apply hanz;simp [hh]
  have hzbound := (show (p a).IsRoot z from hz).norm_lt_cauchyBound hpa
  have hr : ‖z‖<(p a).cauchyBound := by exact_mod_cast hzbound
  exact (hr.trans ha).le

 theorem eval_tendsto_moving {z : A→ℂ} {z₀ : ℂ}
    (hdeg : ∀ a,(p a).natDegree≤N) (hdeg₀ : p₀.natDegree≤N)
    (hc : ∀ j,Tendsto (fun a=>(p a).coeff j) l (𝓝 (p₀.coeff j)))
    (hz : Tendsto z l (𝓝 z₀)) :
    Tendsto (fun a=>(p a).eval (z a)) l (𝓝 (p₀.eval z₀)) := by
  simp_rw [eval_eq_sum_range' (lt_of_le_of_lt (hdeg _) (Nat.lt_succ_self _)),
    eval_eq_sum_range' (lt_of_le_of_lt hdeg₀ (Nat.lt_succ_self _))]
  exact tendsto_finsetSum _ (fun j _=>(hc j).mul (hz.pow j))

/-- Fixed degree prevents roots from escaping to infinity. Every closed
outside-radius root would have a compact cluster point that is a limit root. -/
theorem roots_eventually_lt (hdeg : ∀ a,(p a).natDegree=N) (hdeg₀ : p₀.natDegree=N)
    (hp₀ : p₀≠0) (hc : ∀ j,Tendsto (fun a=>(p a).coeff j) l (𝓝 (p₀.coeff j)))
    {r : ℝ} (hr : ∀ z : ℂ,p₀.eval z=0 → ‖z‖<r) :
    ∀ᶠ a in l,∀ z : ℂ,(p a).eval z=0 → ‖z‖<r := by
  classical
  by_contra h
  have hf : ∃ᶠ a in l,∃ z : ℂ,(p a).eval z=0 ∧ r≤‖z‖ := by
    have hh := not_eventually.mp h
    exact hh.mono (fun a ha=>by push Not at ha;exact ha)
  let B : Set A := {a | ∃ z : ℂ,(p a).eval z=0 ∧ r≤‖z‖}
  let L : Filter A := l⊓𝓟 B
  have : NeBot L := frequently_mem_iff_neBot.mp hf
  let z : A→ℂ := fun a=>if ha : a∈B then Classical.choose ha else 0
  have hz (a : A) (ha : a∈B) : (p a).eval (z a)=0 ∧ r≤‖z a‖ := by
    simpa only [z,dite_eq_left ha] using Classical.choose_spec ha
  have hB : ∀ᶠ a in L,a∈B :=
    (show ∀ᶠ a in 𝓟 B,a∈B by simp).filter_mono inf_le_right
  obtain ⟨R,hR⟩ := roots_eventually_bounded hdeg hdeg₀ hp₀ hc
  have hmem : ∀ᶠ a in L,z a∈Metric.closedBall (0:ℂ) R := by
    filter_upwards [hB,hR.filter_mono inf_le_left] with a ha hbound
    exact mem_closedBall_zero_iff.mpr (hbound _ (hz a ha).1)
  obtain ⟨z₀,_,hcluster⟩ := (isCompact_closedBall (0:ℂ) R).exists_mapClusterPt
    (Filter.tendsto_principal.mpr hmem)
  obtain ⟨U,hUL,hzlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hUl : (U:Filter A)≤l := hUL.trans inf_le_left
  have hBU : ∀ᶠ a in (U:Filter A),a∈B := hB.filter_mono hUL
  have hrootU : ∀ᶠ a in (U:Filter A),(p a).eval (z a)=0 := hBU.mono (fun a ha=>(hz a ha).1)
  have hnormU : ∀ᶠ a in (U:Filter A),r≤‖z a‖ := hBU.mono (fun a ha=>(hz a ha).2)
  have heval := eval_tendsto_moving (fun a=>(hdeg a).le) hdeg₀.le
    (fun j=>(hc j).mono_left hUl) hzlim
  have heq : (fun a=>(p a).eval (z a))=ᶠ[(U:Filter A)] (fun _=>0) := hrootU
  have hzero : p₀.eval z₀=0 := tendsto_nhds_unique heval (tendsto_const_nhds.congr' heq.symm)
  have hnorm : r≤‖z₀‖ := ge_of_tendsto hzlim.norm hnormU
  exact (not_lt_of_ge hnorm) (hr z₀ hzero)

end Complex
end
end nesterov.Slow
