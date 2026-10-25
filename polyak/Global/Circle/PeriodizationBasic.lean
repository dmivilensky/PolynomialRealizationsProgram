import polyak.Global.Circle.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Order.Floor.Ring

/-! Smooth periodization of an actual compactly supported real density.
Local finiteness is proved explicitly, rather than assumed for the series. -/
noncomputable section
namespace polyak.Global.Circle
open Set Filter Function
open scoped Topology ContDiff

def periodize (f : ℝ→ℝ) (x : ℝ) : ℝ:=∑'k : ℤ,f (x+2*Real.pi*k)

theorem periodize_local_finite {f : ℝ→ℝ} {R : ℝ}
    (hf : ∀x,f x≠0→|x|≤R) (x : ℝ) :
    ∃S : Finset ℤ,∀ᶠy in 𝓝 x,∀k : ℤ,k∉S→f (y+2*Real.pi*k)=0 := by
  obtain ⟨N,hN⟩:=exists_nat_gt ((R+|x|+2)/(2*Real.pi))
  let S:Finset ℤ:=(Set.finite_Icc (-(N:ℤ)) (N:ℤ)).toFinset
  refine ⟨S,?_⟩
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
  intro k hk
  by_contra hn
  have hfy:=hf _ hn
  have hnear : |y-x|<1:=by simpa only [Metric.mem_ball,Real.dist_eq] using hy
  have hyabs : |y|< |x|+1 := by
    have hh:=abs_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have hkabs : (N:ℤ)< |k| := by
    apply lt_of_not_ge
    intro habs
    apply hk
    change k∈(Set.finite_Icc (-(N:ℤ)) (N:ℤ)).toFinset
    simpa only [Set.Finite.mem_toFinset,Set.mem_Icc] using abs_le.mp habs
  have hkabsR : (N:ℝ)< |(k:ℝ)|:=by exact_mod_cast hkabs
  have htri : |2*Real.pi*(k:ℝ)|≤|y+2*Real.pi*k|+|y| := by
    have hh:=abs_sub (y+2*Real.pi*(k:ℝ)) y
    simpa only [add_sub_cancel_left] using hh
  rw [abs_mul,abs_of_pos Real.two_pi_pos] at htri
  have hNb : R+|x|+2<(N:ℝ)*(2*Real.pi):=(div_lt_iff₀ Real.two_pi_pos).mp hN
  have hmul:=mul_lt_mul_of_pos_left hkabsR Real.two_pi_pos
  nlinarith

theorem smooth_periodize {f : ℝ→ℝ} {R : ℝ} (hs : ContDiff ℝ ∞ f)
    (hf : ∀x,f x≠0→|x|≤R) : ContDiff ℝ ∞ (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨S,hS⟩:=periodize_local_finite hf x
  have he : periodize f=ᶠ[𝓝 x] (fun y=>∑k∈S,f (y+2*Real.pi*k)) := by
    filter_upwards [hS] with y hy
    exact tsum_eq_sum hy
  have hfinite : ContDiff ℝ ∞ (fun y : ℝ=>∑k∈S,f (y+2*Real.pi*k)) :=
    ContDiff.sum (fun k _=>hs.comp (contDiff_id.add contDiff_const))
  exact hfinite.contDiffAt.congr_of_eventuallyEq he

theorem periodize_periodic (f : ℝ→ℝ) : Function.Periodic (periodize f) (2*Real.pi) := by
  intro x
  unfold periodize
  have hh:=(Equiv.addRight (1:ℤ)).tsum_eq (fun k : ℤ=>f (x+2*Real.pi*k))
  rw [←hh]
  apply tsum_congr
  intro k
  congr 1
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  ring

theorem periodize_nonneg {f : ℝ→ℝ} (hf : ∀x,0≤f x) (x : ℝ) : 0≤periodize f x :=
  tsum_nonneg (fun _=>hf _)

theorem periodize_even {f : ℝ→ℝ} (hf : ∀x,f (-x)=f x) (x : ℝ) :
    periodize f (-x)=periodize f x := by
  unfold periodize
  have he:=(Equiv.neg ℤ).tsum_eq (fun k : ℤ=>f (x+2*Real.pi*k))
  rw [←he]
  apply tsum_congr
  intro k
  have hid : -x+2*Real.pi*(k:ℝ)= -(x+2*Real.pi*((-k:ℤ):ℝ)):=by push_cast; ring
  rw [hid,hf]
  rfl

theorem periodize_eq_on_fundamental {f : ℝ→ℝ} {R : ℝ}
    (hR : R<Real.pi) (hf : ∀x,f x≠0→|x|≤R) {x : ℝ} (hx : x∈Icc (-Real.pi) Real.pi) :
    periodize f x=f x := by
  unfold periodize
  rw [tsum_eq_single (0:ℤ)]
  · simp only [Int.cast_zero,mul_zero,add_zero]
  · intro k hk
    by_contra hn
    have hbound:=hf _ hn
    have hki : (1:ℤ)≤|k|:=Int.one_le_abs hk
    have hkr : (1:ℝ)≤|(k:ℝ)|:=by exact_mod_cast hki
    have htri : |2*Real.pi*(k:ℝ)|≤|x+2*Real.pi*k|+|x| := by
      have hh:=abs_sub (x+2*Real.pi*(k:ℝ)) x
      simpa only [add_sub_cancel_left] using hh
    rw [abs_mul,abs_of_pos Real.two_pi_pos] at htri
    have hxabs : |x|≤Real.pi:=abs_le.mpr hx
    have hmul:=mul_le_mul_of_nonneg_left hkr Real.two_pi_pos.le
    nlinarith

end polyak.Global.Circle
