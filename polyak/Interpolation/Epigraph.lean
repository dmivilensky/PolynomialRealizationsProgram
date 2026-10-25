import polyak.Interpolation.Data
import polyak.Interpolation.Minimum
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
Article: Appendix A, construction (extension).
Use: the proper closed epigraph of the possibly infinite supremum of quadratics.
Proof: work with all real upper bounds instead of pretending an unbounded
supremum is a real-valued function. Strong convexity gives direct minimization.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace polyak.Interpolation

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: the quadratics in (extension). Use: affine plus squared-norm form. -/
def quadraticTerm (x G : I → E) (F : I → ℝ) (i : I) (y : E) : ℝ :=
  inner ℝ (x i - (1 / 2 : ℝ) • G i) y + (1 / 4 : ℝ) * ‖y‖ ^ 2 +
    (1 / 4 : ℝ) * ‖G i‖ ^ 2 - F i

/-- Article: (extension). Proof: expansion of a squared distance. -/
theorem quadraticTerm_eq (x G : I → E) (F : I → ℝ) (i : I) (y : E) :
    quadraticTerm x G F i y = inner ℝ (x i) y - F i +
      (1 / 4 : ℝ) * ‖y - G i‖ ^ 2 := by
  simp only [quadraticTerm, inner_sub_left, real_inner_smul_left, norm_sub_sq_real]
  rw [real_inner_comm y (G i)]
  ring

/-- Article: strong convexity of H. Proof: the exact quadratic mixing identity. -/
theorem norm_mix_sq (y z : E) (a : ℝ) :
    ‖(1 - a) • y + a • z‖ ^ 2 = (1 - a) * ‖y‖ ^ 2 + a * ‖z‖ ^ 2 -
      a * (1 - a) * ‖y - z‖ ^ 2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right, norm_sub_sq_real]
  ring

/-- Article: strong convexity of H. Proof: the affine parts mix exactly. -/
theorem quadraticTerm_mix (x G : I → E) (F : I → ℝ) (i : I) (y z : E) (a : ℝ) :
    quadraticTerm x G F i ((1 - a) • y + a • z) =
      (1 - a) * quadraticTerm x G F i y + a * quadraticTerm x G F i z -
      (1 / 4 : ℝ) * a * (1 - a) * ‖y - z‖ ^ 2 := by
  simp only [quadraticTerm, norm_mix_sq, inner_add_right, inner_smul_right]
  ring

/-- Article: the epigraph of H(y) - ⟨u,y⟩. Use: supports infinite and unbounded tables. -/
def shiftedEpigraph (x G : I → E) (F : I → ℝ) (u : E) : Set (E × ℝ) :=
  {p | ∀ i, quadraticTerm x G F i p.1 - inner ℝ u p.1 ≤ p.2}

/-- Article: lower semicontinuity in Appendix A. Proof: intersection of closed sublevel sets. -/
theorem shiftedEpigraph_closed (x G : I → E) (F : I → ℝ) (u : E) :
    IsClosed (shiftedEpigraph x G F u) := by
  change IsClosed {p : E × ℝ | ∀ i, _}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_snd
  unfold quadraticTerm
  fun_prop

/-- Article: strong convexity of H. Use: quantitative epigraph convexity. -/
theorem shiftedEpigraph_mix (x G : I → E) (F : I → ℝ) (u : E)
    {p q : E × ℝ} (hp : p ∈ shiftedEpigraph x G F u)
    (hq : q ∈ shiftedEpigraph x G F u) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    ((1 - a) • p.1 + a • q.1,
      (1 - a) * p.2 + a * q.2 - (1 / 4 : ℝ) * a * (1 - a) * ‖p.1 - q.1‖ ^ 2) ∈
      shiftedEpigraph x G F u := by
  intro i
  simp only [quadraticTerm_mix, inner_add_right, inner_smul_right]
  have hpi := mul_le_mul_of_nonneg_left (hp i) (sub_nonneg.mpr ha')
  have hqi := mul_le_mul_of_nonneg_left (hq i) ha
  linarith

/-- Article: convexity of the supremum in (extension).
Use: the epigraph is convex in the ordinary product vector space.
Proof: discard the nonnegative strong-convexity improvement in the mixing estimate. -/
theorem shiftedEpigraph_convex (x G : I → E) (F : I → ℝ) (u : E) :
    Convex ℝ (shiftedEpigraph x G F u) := by
  intro p hp q hq a b ha hb hab
  have hb' : b ≤ 1 := by linarith
  have hm := shiftedEpigraph_mix x G F u hp hq hb hb'
  have he : 1 - b = a := by linarith
  rw [he] at hm
  intro i
  have hi := hm i
  change quadraticTerm x G F i (a • p.1 + b • q.1) -
    inner ℝ u (a • p.1 + b • q.1) ≤ a * p.2 + b * q.2
  have hc : 0 ≤ (1 / 4 : ℝ) * b * a * ‖p.1 - q.1‖ ^ 2 := by positivity
  dsimp only at hi
  linarith

/-- Article: H is finite at each prescribed gradient. Proof: (convexinterp). -/
theorem shiftedEpigraph_datum {x G : I → E} {F : I → ℝ}
    (h : ConvexTableFeasible x G F) (u : E) (j : I) :
    (G j, inner ℝ (x j) (G j) - F j - inner ℝ u (G j)) ∈ shiftedEpigraph x G F u := by
  intro i
  rw [quadraticTerm_eq]
  have hij := h i j
  rw [norm_sub_rev (G j) (G i)]
  simp only [inner_sub_right] at hij
  rw [real_inner_comm (x i) (G j), real_inner_comm (x j) (G j)] at hij
  linarith

/-- Article: the supremum is attained at every prescribed gradient.
Use: exact properness of the infinite quadratic supremum, with no global finiteness assumption.
Proof: convex interpolation gives the upper bound, and the datum's own term attains it. -/
theorem quadraticTerm_datum_isLUB {x G : I → E} {F : I → ℝ}
    (h : ConvexTableFeasible x G F) (j : I) :
    IsLUB (Set.range fun i => quadraticTerm x G F i (G j))
      (inner ℝ (x j) (G j) - F j) := by
  constructor
  · rintro r ⟨i, rfl⟩
    have hi := shiftedEpigraph_datum h (0 : E) j i
    simpa only [inner_zero_left, sub_zero] using hi
  · intro b hb
    have hi := hb (Set.mem_range_self j)
    simpa [quadraticTerm_eq] using hi

/-- Article: H(y) ≥ ‖y‖²/4. Use: all shifted minimization problems are bounded below. -/
theorem shiftedEpigraph_bddBelow {x G : I → E} {F : I → ℝ} (star : I)
    (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) (u : E) :
    BddBelow (Prod.snd '' shiftedEpigraph x G F u) := by
  refine ⟨-‖u‖ ^ 2, ?_⟩
  rintro r ⟨p, hp, rfl⟩
  have h := hp star
  simp only [quadraticTerm, hx, hG, hF, smul_zero, sub_zero, inner_zero_left,
    norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add] at h
  have hi := real_inner_le_norm u p.1
  nlinarith [sq_nonneg (‖p.1‖ - 2 * ‖u‖)]

variable [CompleteSpace E]

/-- Article: minimization in Appendix A. Use: a single minimizer for every dual point.
Proof: the direct strongly-convex-epigraph minimum theorem. -/
theorem shiftedEpigraph_hasMin {x G : I → E} {F : I → ℝ}
    (h : ConvexTableFeasible x G F) (star : I)
    (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) (u : E) :
    ∃ p ∈ shiftedEpigraph x G F u, ∀ q ∈ shiftedEpigraph x G F u, p.2 ≤ q.2 := by
  apply exists_min_height (c := 1 / 16)
    ⟨_, shiftedEpigraph_datum h u star⟩ (shiftedEpigraph_closed x G F u)
    (shiftedEpigraph_bddBelow star hx hG hF u) (by norm_num)
  intro p hp q hq
  convert shiftedEpigraph_mix x G F u hp hq (a := 1 / 2) (by norm_num) (by norm_num) using 1
  congr 1
  · module
  · ring

omit [CompleteSpace E] in
/-- Article: strong convexity at the optimizer. Use: sharp strong support inequality.
Proof: mix with any comparison point, cancel the positive mixing coefficient,
and send it to zero; the coefficient is preserved exactly. -/
theorem min_height_strong {x G : I → E} {F : I → ℝ} {u : E} {p : E × ℝ}
    (hp : p ∈ shiftedEpigraph x G F u)
    (hmin : ∀ q ∈ shiftedEpigraph x G F u, p.2 ≤ q.2)
    (q : E × ℝ) (hq : q ∈ shiftedEpigraph x G F u) :
    p.2 + (1 / 4 : ℝ) * ‖p.1 - q.1‖ ^ 2 ≤ q.2 := by
  have hn (n : ℕ) : p.2 + (1 / 4 : ℝ) * (1 - 1 / ((n : ℝ) + 1)) *
      ‖p.1 - q.1‖ ^ 2 ≤ q.2 := by
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have ha' : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hnat : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hh := hmin _ (shiftedEpigraph_mix x G F u hp hq (le_of_lt ha) ha')
    dsimp only at hh
    nlinarith
  have ht : Tendsto (fun n : ℕ => p.2 + (1 / 4 : ℝ) * (1 - 1 / ((n : ℝ) + 1)) *
      ‖p.1 - q.1‖ ^ 2) atTop (𝓝 (p.2 + (1 / 4 : ℝ) * ‖p.1 - q.1‖ ^ 2)) := by
    have hlim := (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1).const_mul
      (1 / 4 : ℝ)).mul_const (‖p.1 - q.1‖ ^ 2)
    have hlim' := hlim.const_add p.2
    simpa using hlim'
  exact le_of_tendsto' ht hn

end polyak.Interpolation
