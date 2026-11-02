import krylov.Reference.CG
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, genuine reference CG geometry.
Use: prove conjugacy, orthogonality and positive line lengths from the actual
Fletcher--Reeves recurrence; no orthogonal reference frame is assumed here.
Source: the classical exact-arithmetic CG induction, HestenesStiefel52 and Meurant06.
-/

namespace krylov.Reference.CG
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual gradient of the concrete CG run.
Use: readable finite-prefix geometry statements about the genuine recurrence.
Article: main_krylov, s2:eq:cg, g_k⁰. -/
abbrev gradient (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E := (cgRun Q g k).gradient

/-- The actual direction of the concrete CG run.
Use: all conjugacy statements concern real computed query directions.
Article: main_krylov, s2:eq:cg, d_k⁰. -/
abbrev direction (Q : E →L[ℝ] E) (g : E) (k : ℕ) : E := (cgRun Q g k).direction

/-- The actual line length of the concrete CG run.
Use: prove positivity before dividing its true secant action.
Article: main_krylov, s2:eq:cg, α_k. -/
abbrev length (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  lineLength (gradient Q g k) (direction Q g k) (Q (direction Q g k))

/-- The actual residual-norm recurrence coefficient.
Use: compute conjugacy of each actual newly generated direction.
Article: main_krylov, s2:eq:cg, standard Fletcher--Reeves coefficient. -/
abbrev beta (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  ‖gradient Q g (k+1)‖^2/‖gradient Q g k‖^2

/-- The actual gradient recurrence is the actual exact-search oracle update.
Use: relates Qd_i to two consecutive actual gradients.
Article: main_krylov, s2:eq:cg.
Proof: unfold one concrete CG update. -/
theorem gradient_succ (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    gradient Q g (k+1)=gradient Q g k+length Q g k • Q (direction Q g k) := rfl

/-- The actual direction recurrence uses the actual new gradient and actual residual-norm coefficient.
Use: all later orthogonality calculations follow from this executed recurrence.
Article: main_krylov, s2:eq:cg.
Proof: unfold one concrete CG direction update. -/
theorem direction_succ (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    direction Q g (k+1)= -gradient Q g (k+1)+beta Q g k • direction Q g k := rfl

/-- The actual consecutive gradient difference is the true line-scaled operator action.
Use: substitute old operator actions into actual residual orthogonality identities.
Article: main_krylov, s2:eq:cg.
Proof: subtract the preceding actual gradient from its true update. -/
theorem gradient_change (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    gradient Q g (k+1)-gradient Q g k=length Q g k • Q (direction Q g k) := by
  rw [gradient_succ]
  abel

/-- Simultaneous exact geometric invariants of the actual finite CG prefix.
Use: this proposition is proved by induction, rather than postulated as reference trajectory data.
Article: main_krylov, s2:eq:cg, exact-arithmetic reference geometry. -/
structure Invariant (Q : E →L[ℝ] E) (g : E) (k : ℕ) : Prop where
  /-- The actual current direction has the exact negative residual-energy pairing. -/
  search_pair : inner ℝ (direction Q g k) (gradient Q g k)= -‖gradient Q g k‖^2
  /-- The current actual residual is orthogonal to all earlier actual directions. -/
  old_direction : ∀ i<k, inner ℝ (direction Q g i) (gradient Q g k)=0
  /-- The current actual residual is orthogonal to all earlier actual residuals. -/
  old_gradient : ∀ i<k, inner ℝ (gradient Q g i) (gradient Q g k)=0
  /-- Every pair of true generated directions is conjugate through the actual positive operator. -/
  conjugate : ∀ i j, i<j → j≤k → inner ℝ (direction Q g i) (Q (direction Q g j))=0
  /-- Every true line already performed in the nondegenerate prefix is strictly positive. -/
  lines_pos : ∀ i<k, 0<length Q g i

/-- The actual initial CG state has the geometric invariants before any oracle update.
Use: start the simultaneous proof without an assumed reference frame.
Article: main_krylov, s2:eq:cg.
Proof: its actual direction is the negative actual initial gradient; every earlier-prefix condition is empty. -/
theorem invariant_zero (Q : E →L[ℝ] E) (g : E) : Invariant Q g 0 := by
  refine ⟨?_, by omega, by omega, by omega, by omega⟩
  change inner ℝ (-g) g= -‖g‖^2
  rw [inner_neg_left, real_inner_self_eq_norm_sq]

/-- A true nonzero residual gives a true nonzero direction and a true positive reference line.
Use: actual CG denominators are justified before they enter the geometric induction.
Article: main_krylov, s2:eq:cg, nondegenerate positive line search.
Proof: its exact search pairing rules out a zero direction; positivity gives
positive curvature, so the real line formula is the positive residual energy divided by that curvature. -/
theorem invariant_line_pos (Q : E →L[ℝ] E)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hk : Invariant Q g k) (hg : gradient Q g k≠0) :
    direction Q g k≠0 ∧ 0<length Q g k ∧
      length Q g k=‖gradient Q g k‖^2/inner ℝ (direction Q g k) (Q (direction Q g k)) := by
  -- Nonzero actual residual energy first rules out a zero true search direction.
  have hn : 0<‖gradient Q g k‖ := norm_pos_iff.mpr hg
  have hd : direction Q g k≠0 := by
    intro hz
    have he := hk.search_pair
    rw [hz, inner_zero_left] at he
    nlinarith
  have hc := hpos (direction Q g k) hd
  have hl : length Q g k=‖gradient Q g k‖^2/inner ℝ (direction Q g k) (Q (direction Q g k)) := by
    change -inner ℝ (direction Q g k) (gradient Q g k)/_= _
    rw [hk.search_pair, neg_neg]
  exact ⟨hd, hl.symm ▸ div_pos (sq_pos_of_pos hn) hc, hl⟩

/-- A genuine nondegenerate CG update preserves all actual conjugacy/orthogonality invariants.
Use: produces the real canonical orthogonal reference steps needed by the terminal data fibre.
Article: main_krylov, s2:eq:cg, classical exact CG induction.
Proof: exact search gives the new direction orthogonality; the executed gradient/direction
recurrences give new residual orthogonality and then conjugacy, with positive true line lengths. -/
theorem invariant_succ (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hk : Invariant Q g k) (hg : gradient Q g k≠0) : Invariant Q g (k+1) := by
  obtain ⟨hd, hlen, hformula⟩ := invariant_line_pos Q hpos g k hk hg
  have hc := hpos (direction Q g k) hd
  have hnorm : ‖gradient Q g k‖≠0 := norm_ne_zero_iff.mpr hg
  have hnewdir (i : ℕ) (hi : i≤k) : inner ℝ (direction Q g i) (gradient Q g (k+1))=0 := by
    rw [gradient_succ, inner_add_right, real_inner_smul_right]
    by_cases he : i=k
    · subst i
      change inner ℝ (direction Q g k) (gradient Q g k)+
        (-inner ℝ (direction Q g k) (gradient Q g k)/inner ℝ (direction Q g k) (Q (direction Q g k)))*
          inner ℝ (direction Q g k) (Q (direction Q g k))=0
      rw [div_mul_cancel₀ _ hc.ne']
      abel
    · rw [hk.old_direction i (by omega), hk.conjugate i k (by omega) le_rfl, mul_zero, add_zero]
  have hnewgrad (i : ℕ) (hi : i≤k) : inner ℝ (gradient Q g i) (gradient Q g (k+1))=0 := by
    cases i with
    | zero =>
      have he : gradient Q g 0= -direction Q g 0 := by change g= -(-g); simp only [neg_neg]
      rw [he, inner_neg_left, hnewdir 0 (by omega), neg_zero]
    | succ i =>
      have he : gradient Q g (i+1)= -direction Q g (i+1)+beta Q g i • direction Q g i := by
        rw [direction_succ]
        module
      rw [he, inner_add_left, inner_neg_left, real_inner_smul_left,
        hnewdir (i+1) hi, hnewdir i (by omega), neg_zero, mul_zero, add_zero]
  -- The true old operator actions are consecutive true residual differences divided by proved positive lines.
  have haction (i : ℕ) : length Q g i*inner ℝ (direction Q g i) (Q (gradient Q g (k+1)))=
      inner ℝ (gradient Q g (i+1)) (gradient Q g (k+1))-
        inner ℝ (gradient Q g i) (gradient Q g (k+1)) := by
    have he := hQ (direction Q g i) (gradient Q g (k+1))
    change inner ℝ (Q (direction Q g i)) (gradient Q g (k+1))=
      inner ℝ (direction Q g i) (Q (gradient Q g (k+1))) at he
    rw [← he, ← real_inner_smul_left,
      ← gradient_change, inner_sub_left]
  have hconj (i : ℕ) (hi : i≤k) : inner ℝ (direction Q g i) (Q (direction Q g (k+1)))=0 := by
    rw [direction_succ, map_add, map_neg, map_smul, inner_add_right, inner_neg_right, real_inner_smul_right]
    have he := haction i
    by_cases hik : i=k
    · subst i
      rw [real_inner_self_eq_norm_sq, hnewgrad k le_rfl, sub_zero] at he
      have hprod : length Q g k*beta Q g k*inner ℝ (direction Q g k) (Q (direction Q g k))=
          ‖gradient Q g (k+1)‖^2 := by
        rw [hformula]
        dsimp only [beta]
        field_simp
      nlinarith
    · rw [hnewgrad (i+1) (by omega), hnewgrad i hi, sub_self] at he
      have hz := (mul_eq_zero.mp he).resolve_left (hk.lines_pos i (by omega)).ne'
      rw [hz, hk.conjugate i k (by omega) le_rfl, neg_zero, mul_zero, add_zero]
  refine ⟨?_, fun i hi => hnewdir i (by omega), fun i hi => hnewgrad i (by omega), ?_, ?_⟩
  · rw [direction_succ, inner_add_left, inner_neg_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hnewdir k le_rfl, mul_zero, add_zero]
  · intro i j hij hj
    by_cases he : j=k+1
    · subst j
      exact hconj i (by omega)
    · exact hk.conjugate i j hij (by omega)
  · intro i hi
    by_cases he : i=k
    · subst i
      exact hlen
    · exact hk.lines_pos i (by omega)

/-- All actual geometric CG invariants hold through every nondegenerate finite prefix.
Use: source reference conjugacy is derived from its genuine recurrence and actual nonstagnation premise.
Article: main_krylov, s2:eq:cg, exact reference CG geometry.
Proof: finite induction uses only true nonzero residuals before the current time,
never an impossible infinite nonstagnation assumption in finite dimension. -/
theorem invariant (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i<k, gradient Q g i≠0) : Invariant Q g k := by
  induction k with
  | zero => exact invariant_zero Q g
  | succ k ih =>
    exact invariant_succ Q hQ hpos g k (ih (fun i hi => hg i (by omega))) (hg k (by omega))

end
end krylov.Reference.CG
