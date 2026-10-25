import polyak.Global.Sampling.ThreeRanges
import polyak.Global.Kernels.Gain
import polyak.Global.Kernels.Variation
import Mathlib.Order.Filter.Finite

/-! One scale works simultaneously for the finite low range, the infinite
middle and high ranges, and the positive minimizer moment. -/
noncomputable section
namespace polyak.Global.Sampling
open Set Filter
open scoped Topology

def lowLagSet (N:ℕ) : Set ℤ := {n | n≠0 ∧ |(n:ℝ)|<(N:ℝ)}

theorem finite_lowLagSet (N:ℕ) : (lowLagSet N).Finite := by
  apply (Set.finite_Icc (-(N:ℤ)) N).subset
  intro n hn
  have hh:=abs_lt.mp hn.2
  constructor
  · exact_mod_cast hh.1.le
  · exact_mod_cast hh.2.le

theorem finite_positive_lower_bound {ι:Type*} {A:Set ι} (hA:A.Finite)
    (f:ι→ℝ) (hf:∀i∈A,0<f i) : ∃a:ℝ,0<a ∧ ∀i∈A,a≤f i := by
  induction A,hA using Set.Finite.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i A hi hA ih =>
    obtain ⟨a,ha,hbound⟩:=ih (fun j hj=>hf j (Set.mem_insert_of_mem i hj))
    refine ⟨min (f i) a,lt_min (hf i (Set.mem_insert i A)) ha,?_⟩
    intro j hj
    rcases hj with rfl|hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound j hj)

theorem exists_small_sampling_scale {c c0 M m R : ℝ}
    (hc:0<c) (hc0:0<c0)
    (μ:ℤ→ℝ)
    (hμ:∀n∈lowLagSet (lagCutoff (c*c0) (6*M*m) (8*M^2*m+R)),0<μ n) :
    ∃ε a:ℝ,0<ε ∧ ε<Real.pi ∧ 0<a ∧
      ε*(lagCutoff (c*c0) (6*M*m) (8*M^2*m+R):ℝ)≤1 ∧
      4*M*ε+R*ε^2≤c*c0/2 ∧
      (2*M^2*m+R/2)*ε^2≤c0/2 ∧
      ∀n∈lowLagSet (lagCutoff (c*c0) (6*M*m) (8*M^2*m+R)),
        a≤μ n ∧ 1/2≤Kernels.kernelHat ε n ∧
          (8*M^2*m+6*M*m*(lagCutoff (c*c0) (6*M*m) (8*M^2*m+R):ℝ)+R)*ε^2≤a/4 := by
  let N:=lagCutoff (c*c0) (6*M*m) (8*M^2*m+R)
  obtain ⟨a,ha,hbound⟩:=finite_positive_lower_bound (finite_lowLagSet N) μ hμ
  have hhat : ∀ᶠε:ℝ in 𝓝 (0:ℝ),∀n∈lowLagSet N,1/2≤Kernels.kernelHat ε n := by
    apply (finite_lowLagSet N).eventually_all.mpr
    intro n _
    have hh := (Kernels.continuous_kernelHat_scale (n:ℝ)).continuousAt.eventually
      (eventually_gt_nhds (show (1/2:ℝ)<Kernels.kernelHat 0 n by simp; norm_num))
    exact hh.mono (fun _ h=>h.le)
  have hhigh : ∀ᶠε:ℝ in 𝓝 (0:ℝ),4*M*ε+R*ε^2≤c*c0/2 := by
    have hh : Continuous (fun ε:ℝ=>4*M*ε+R*ε^2):=by fun_prop
    exact (hh.continuousAt.eventually (eventually_lt_nhds (by simp; positivity))).mono (fun _ h=>h.le)
  have hlow : ∀ᶠε:ℝ in 𝓝 (0:ℝ),(8*M^2*m+6*M*m*(N:ℝ)+R)*ε^2≤a/4 := by
    have hh : Continuous (fun ε:ℝ=>(8*M^2*m+6*M*m*(N:ℝ)+R)*ε^2):=by fun_prop
    exact (hh.continuousAt.eventually (eventually_lt_nhds (by simp; positivity))).mono (fun _ h=>h.le)
  have hmin : ∀ᶠε:ℝ in 𝓝 (0:ℝ),(2*M^2*m+R/2)*ε^2≤c0/2 := by
    have hh : Continuous (fun ε:ℝ=>(2*M^2*m+R/2)*ε^2):=by fun_prop
    exact (hh.continuousAt.eventually (eventually_lt_nhds (by simp; positivity))).mono (fun _ h=>h.le)
  have hcut : ∀ᶠε:ℝ in 𝓝 (0:ℝ),ε*(N:ℝ)≤1 := by
    have hh : Continuous (fun ε:ℝ=>ε*(N:ℝ)):=by fun_prop
    exact (hh.continuousAt.eventually (eventually_lt_nhds (by simp))).mono (fun _ h=>h.le)
  have hpi : ∀ᶠε:ℝ in 𝓝 (0:ℝ),ε<Real.pi := eventually_lt_nhds Real.pi_pos
  have hall : ∀ᶠε:ℝ in 𝓝[>] (0:ℝ),0<ε ∧ ε<Real.pi ∧
      ε*(N:ℝ)≤1 ∧ 4*M*ε+R*ε^2≤c*c0/2 ∧ (2*M^2*m+R/2)*ε^2≤c0/2 ∧
      ∀n∈lowLagSet N,1/2≤Kernels.kernelHat ε n ∧
        (8*M^2*m+6*M*m*(N:ℝ)+R)*ε^2≤a/4 := by
    filter_upwards [self_mem_nhdsWithin, hpi.filter_mono nhdsWithin_le_nhds,
      hcut.filter_mono nhdsWithin_le_nhds,hhigh.filter_mono nhdsWithin_le_nhds,
      hmin.filter_mono nhdsWithin_le_nhds,hhat.filter_mono nhdsWithin_le_nhds,
      hlow.filter_mono nhdsWithin_le_nhds] with ε hε hp hcut hh hg hhat hl
    exact ⟨hε,hp,hcut,hh,hg,fun n hn=>⟨hhat n hn,hl⟩⟩
  obtain ⟨ε,hε,hp,hcut,hh,hg,hl⟩:=hall.exists
  exact ⟨ε,a,hε,hp,ha,hcut,hh,hg,fun n hn=>⟨hbound n hn,(hl n hn).1,(hl n hn).2⟩⟩

end polyak.Global.Sampling
