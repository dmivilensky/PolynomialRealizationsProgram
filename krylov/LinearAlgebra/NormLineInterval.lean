import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(c), compact interval of a relative norm ball.
Use: derive existence of both actual endpoints when an original physical
one-dimensional information fibre meets a genuine metric ball.
Source: the Heine--Borel theorem on the real parameter line and convexity of
a norm sublevel; all boundedness and endpoint hypotheses are proved here.
-/

namespace krylov.LinearAlgebra
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty norm-ball section along a genuine nonconstant affine real line
is exactly an attained compact closed interval, possibly a singleton.
Use: the original relative-ball information interval is constructed from its
actual physical operator norm, with no endpoint structure assumed as input.
Article: main_krylov, s5:fibre(c).
Proof: continuity makes the true sublevel closed; the nonzero line direction
bounds its scalar parameter by the triangle inequality. Heine--Borel supplies
both actual extrema, and norm convexity fills the whole interval between them. -/
theorem norm_line_interval (u v : E) (hv : v≠0) (r : ℝ)
    (hne : ({t : ℝ | ‖u+t • v‖≤r} : Set ℝ).Nonempty) :
    ∃ lo hi : ℝ,lo≤hi ∧ {t : ℝ | ‖u+t • v‖≤r}=Set.Icc lo hi := by
  let S := {t : ℝ | ‖u+t • v‖≤r}
  have hvn : 0<‖v‖ := norm_pos_iff.mpr hv
  have hs : IsClosed S := isClosed_le (continuous_const.add (continuous_id.smul continuous_const)).norm continuous_const
  have hbounded : Bornology.IsBounded S := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mpr
    refine ⟨(r+‖u‖)/‖v‖,?_⟩
    intro t ht
    have hh : ‖t • v‖≤‖u+t • v‖+‖u‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (u+t • v) u
    rw [norm_smul,Real.norm_eq_abs] at hh
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero]
    exact (le_div_iff₀ hvn).mpr (hh.trans (add_le_add ht (le_refl ‖u‖)))
  have hcompact : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hs,hbounded⟩
  have hconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    have hsplit : u+(a*x+b*y) • v=a • (u+x • v)+b • (u+y • v) := by
      have hu : a • u+b • u=u := by rw [← add_smul,hab,one_smul]
      calc
        _ = (a • u+b • u)+(a*x+b*y) • v := by rw [hu]
        _ = _ := by module
    change ‖u+(a*x+b*y) • v‖≤r
    calc
      _ = ‖a • (u+x • v)+b • (u+y • v)‖ := congrArg norm hsplit
      _ ≤ ‖a • (u+x • v)‖+‖b • (u+y • v)‖ := norm_add_le _ _
      _ = a*‖u+x • v‖+b*‖u+y • v‖ := by
        rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
      _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = r := by rw [← add_mul,hab,one_mul]
  obtain ⟨lo,hlo⟩ := hcompact.exists_isLeast hne
  obtain ⟨hi,hhi⟩ := hcompact.exists_isGreatest hne
  refine ⟨lo,hi,hlo.2 hhi.1,?_⟩
  apply Set.Subset.antisymm
  · intro t ht
    exact ⟨hlo.2 ht,hhi.2 ht⟩
  · exact hconv.ordConnected.out hlo.1 hhi.1

end
end krylov.LinearAlgebra
