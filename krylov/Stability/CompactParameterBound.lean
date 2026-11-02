import krylov.Stability.CompactEventual
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), uniform arbitrary compact parameters.
Use: actual Broyden interpolation parameters need not have a limit or any
regularity; only the genuine primitive observed pair data must converge.
Source: compact image bounds and the existing compact neighborhood tube.
-/

namespace krylov.Stability
noncomputable section
open Set Filter Topology Asymptotics
variable {R P F α : Type*} [NormedAddCommGroup R] [NormedAddCommGroup P]
variable [NormedAddCommGroup F]

/-- A genuine jointly continuous field is bounded along arbitrary compact
parameter choices and convergent primitive data, without any regularity
or limiting assumption on the actual compact parameter schedule.
Use: derive native uniform model and inverse-curvature bounds for all
original convex Broyden schedules, including discontinuous schedules.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the genuine compact reference image is bounded. Continuity gives
a neighborhood bound there; the proved compact tube makes its radius
common. The actual convergent data eventually enter that tube. -/
theorem compact_parameter_bigO (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (p0 : P) (hf : ∀ x∈K,ContinuousAt f (x,p0)) (l : Filter α)
    (a : α → R) (p : α → P) (ha : ∀ᶠ z in l,a z∈K) (hp : Tendsto p l (𝓝 p0)) :
    (fun z => f (a z,p z)) =O[l] (fun _ => (1 : ℝ)) := by
  have hcont : ContinuousOn (fun x => f (x,p0)) K := by
    intro x hx
    have hm : ContinuousAt (fun y : R => (y,p0)) x := continuousAt_id.prodMk continuousAt_const
    exact ((hf x hx).comp (f := fun y : R => (y,p0)) hm).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hcont
  have he (x : R) (hx : x∈K) :
      ∀ᶠ z in 𝓝 (x,(0 : P)),‖f (z.1,z.2+p0)‖<M+1 := by
    have hc : ContinuousAt (fun z : R × P => f (z.1,z.2+p0)) (x,0) :=
      (hf x hx).comp_of_eq (f := fun z : R × P => (z.1,z.2+p0))
        (continuousAt_fst.prodMk (continuousAt_snd.add continuousAt_const)) (by simp only [zero_add])
    exact hc.norm.eventually (gt_mem_nhds (by
      simpa only [zero_add] using lt_add_of_le_of_pos (hM x hx) zero_lt_one))
  obtain ⟨delta,hd,hbound⟩ := compact_reference_eventual_tube
    (fun z : R × P => ‖f (z.1,z.2+p0)‖<M+1) K hK he
  have ht : Tendsto (fun z => ‖p z-p0‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hp.sub (tendsto_const_nhds (x := p0))).norm
  have hnear : ∀ᶠ z in l,‖p z-p0‖<delta := (tendsto_order.mp ht).2 delta hd
  apply IsBigO.of_bound (M+1)
  filter_upwards [ha,hnear] with z hz hn
  have h := hbound (a z) hz 0 (p z-p0) (by
    simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using hn.le)
  simpa only [add_zero,sub_add_cancel,norm_one,mul_one] using h.le

end
end krylov.Stability
