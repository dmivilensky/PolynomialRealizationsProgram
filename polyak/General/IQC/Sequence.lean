import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Article: Appendix D, the finite truncations used in Lemma homotopy.
The sequence is unrestricted; square summability is proved from bounds on
all finite truncations, never assumed for the unknown closed-loop solution.
-/

noncomputable section
namespace polyak.General.IQC
open Finset Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

def truncate (N : ℕ) (x : ℕ → E) : ℕ → E := fun k => if k<N then x k else 0

def prefixNorm (x : ℕ → E) (N : ℕ) : ℝ :=
  ‖WithLp.toLp 2 (fun k : Fin N => x k)‖

def SquareSummable (x : ℕ → E) : Prop := Summable (fun k => ‖x k‖^2)

def sequenceNorm (x : ℕ → E) : ℝ := Real.sqrt (∑' k,‖x k‖^2)

theorem sequenceNorm_nonneg (x : ℕ → E) : 0≤sequenceNorm x := Real.sqrt_nonneg _

theorem prefixNorm_nonneg (x : ℕ → E) (N : ℕ) : 0≤prefixNorm x N := norm_nonneg _

theorem prefixNorm_sq (x : ℕ → E) (N : ℕ) :
    prefixNorm x N^2=∑ k∈range N,‖x k‖^2 := by
  rw [prefixNorm,PiLp.norm_sq_eq_of_L2]
  exact Fin.sum_univ_eq_sum_range (fun k => ‖x k‖^2) N

theorem prefixNorm_congr {x y : ℕ → E} {N : ℕ} (h : ∀ k<N,x k=y k) :
    prefixNorm x N=prefixNorm y N := by
  have he : (fun k : Fin N => x k)=(fun k : Fin N => y k) :=
    funext (fun k => h k k.isLt)
  simp only [prefixNorm,he]

theorem prefixNorm_triangle (x y : ℕ → E) (N : ℕ) :
    prefixNorm (x+y) N≤prefixNorm x N+prefixNorm y N := by
  exact norm_add_le (WithLp.toLp 2 (fun k : Fin N => x k))
    (WithLp.toLp 2 (fun k : Fin N => y k))

@[simp] theorem prefixNorm_zero (N : ℕ) : prefixNorm (0 : ℕ → E) N=0 := by
  change ‖(0 : PiLp 2 (fun _ : Fin N => E))‖=0
  exact norm_zero

@[simp] theorem prefixNorm_truncate (x : ℕ → E) (N : ℕ) :
    prefixNorm (truncate N x) N=prefixNorm x N :=
  prefixNorm_congr (fun _ hk => ite_eq_left hk)

theorem prefixNorm_mono {x : ℕ → E} {N M : ℕ} (hNM : N≤M) :
    prefixNorm x N≤prefixNorm x M := by
  apply (sq_le_sq₀ (prefixNorm_nonneg _ _) (prefixNorm_nonneg _ _)).mp
  rw [prefixNorm_sq,prefixNorm_sq]
  exact sum_le_sum_of_subset_of_nonneg (range_mono hNM) (fun _ _ _ => sq_nonneg _)

theorem prefixNorm_le_of_pointwise {x y : ℕ → E} {N : ℕ}
    (h : ∀ k<N,‖x k‖≤‖y k‖) : prefixNorm x N≤prefixNorm y N := by
  apply (sq_le_sq₀ (prefixNorm_nonneg _ _) (prefixNorm_nonneg _ _)).mp
  rw [prefixNorm_sq,prefixNorm_sq]
  exact sum_le_sum fun k hk => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (h k (mem_range.mp hk))

theorem squareSummable_of_prefix_bound {x : ℕ → E} {C : ℝ}
    (h : ∀ N,prefixNorm x N≤C) : SquareSummable x := by
  have hC : 0≤C := (prefixNorm_nonneg x 0).trans (h 0)
  apply summable_of_sum_range_le (c:=C^2) (fun k => sq_nonneg _)
  intro N
  rw [←prefixNorm_sq]
  exact (sq_le_sq₀ (prefixNorm_nonneg _ _) hC).mpr (h N)

theorem SquareSummable.prefix_bound {x : ℕ → E} (hx : SquareSummable x) :
    ∃ C : ℝ,0≤C ∧ ∀ N,prefixNorm x N≤C := by
  refine ⟨Real.sqrt (∑' k,‖x k‖^2),Real.sqrt_nonneg _,fun N => ?_⟩
  apply (sq_le_sq₀ (prefixNorm_nonneg _ _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (tsum_nonneg (fun k => sq_nonneg _)),prefixNorm_sq]
  exact hx.sum_le_tsum (range N) (fun k _ => sq_nonneg _)

theorem squareSummable_truncate (x : ℕ → E) (N : ℕ) : SquareSummable (truncate N x) := by
  apply summable_of_ne_finset_zero (s:=range N)
  intro k hk
  simp [truncate,show ¬k<N from fun h => hk (mem_range.mpr h)]

theorem prefixNorm_le_sequenceNorm {x : ℕ → E} (hx : SquareSummable x) (N : ℕ) :
    prefixNorm x N≤sequenceNorm x := by
  apply (sq_le_sq₀ (prefixNorm_nonneg _ _) (sequenceNorm_nonneg _)).mp
  rw [sequenceNorm,Real.sq_sqrt (tsum_nonneg (fun k => sq_nonneg _)),prefixNorm_sq]
  exact hx.sum_le_tsum (range N) (fun k _ => sq_nonneg _)

theorem sequenceNorm_truncate (x : ℕ → E) (N : ℕ) :
    sequenceNorm (truncate N x)=prefixNorm x N := by
  have he : (∑' k,‖truncate N x k‖^2)=∑ k∈range N,‖x k‖^2 := by
    rw [tsum_eq_sum (s:=range N)]
    · exact sum_congr rfl fun k hk => by rw [truncate,ite_eq_left (mem_range.mp hk)]
    · intro k hk
      simp [truncate,show ¬k<N from fun h => hk (mem_range.mpr h)]
  rw [sequenceNorm,he,←prefixNorm_sq,Real.sqrt_sq (prefixNorm_nonneg _ _)]

theorem sequenceNorm_le_of_prefix_bound {x : ℕ → E} {C : ℝ} (hC : 0≤C)
    (h : ∀ N,prefixNorm x N≤C) : sequenceNorm x≤C := by
  have hs:=squareSummable_of_prefix_bound h
  have ht : (∑' k,‖x k‖^2)≤C^2 := by
    apply hs.tsum_le_of_sum_range_le
    intro N
    rw [←prefixNorm_sq]
    exact (sq_le_sq₀ (prefixNorm_nonneg _ _) hC).mpr (h N)
  exact (Real.sqrt_le_sqrt ht).trans_eq (Real.sqrt_sq hC)

variable [NormedSpace ℝ E]

@[simp] theorem prefixNorm_smul (r : ℝ) (x : ℕ → E) (N : ℕ) :
    prefixNorm (r • x) N=|r| * prefixNorm x N := by
  unfold prefixNorm
  have he : WithLp.toLp 2 (fun k : Fin N => (r • x) k)=
      r • WithLp.toLp 2 (fun k : Fin N => x k) := by
    apply WithLp.ofLp_injective 2
    funext _k
    rfl
  rw [he,norm_smul,Real.norm_eq_abs]

theorem SquareSummable.smul {x : ℕ → E} (hx : SquareSummable x) (r : ℝ) :
    SquareSummable (r • x) := by
  obtain ⟨C,hC,hb⟩:=hx.prefix_bound
  apply squareSummable_of_prefix_bound (C:=|r| * C)
  intro N
  rw [prefixNorm_smul]
  exact mul_le_mul_of_nonneg_left (hb N) (abs_nonneg _)

omit [NormedSpace ℝ E] in
theorem SquareSummable.add {x y : ℕ → E} (hx : SquareSummable x) (hy : SquareSummable y) :
    SquareSummable (x+y) := by
  obtain ⟨C,_,hc⟩:=hx.prefix_bound
  obtain ⟨D,_,hd⟩:=hy.prefix_bound
  exact squareSummable_of_prefix_bound (fun N =>
    (prefixNorm_triangle x y N).trans (add_le_add (hc N) (hd N)))

end polyak.General.IQC
