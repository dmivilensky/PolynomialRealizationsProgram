import jacobi.Rearrangement.Polarization
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Two-point sorting is nonexpansive in L1 and in the uniform norm. It preserves
the Lipschitz constant of a real function, including across the reflection
boundary. These analytic estimates support approximation and compactness in
the limiting symmetric rearrangement construction.
Source: elementary contraction estimates for order statistics and one-dimensional Lipschitz gluing.
Use: pointwise contraction of the reflected density pairs in L1.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory Real Set
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

/-- Sorted matching minimizes the sum of the two absolute matching distances.
Use: pointwise contraction of the reflected density pairs in L1.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: split the finite order cases; each branch is a linear real inequality. -/
theorem sorted_pair_distance (a b c d : ℝ) :
    |max a b-max c d|+|min a b-min c d| ≤ |a-c|+|b-d| := by
  grind [abs_eq_max_neg]

/-- Polarizing both functions contracts the sum of distances on each reflected pair.
Use: nonexpansivity of the actual polarization map in L1.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: on the preferred half-line apply sorted matching; otherwise reflect the
point to that half-line and commute the two summands. -/
theorem polarize_distance_pair (a : ℝ) (m q : ℝ → ℝ) (x : ℝ) :
    |polarize a m x-polarize a q x|+
      |polarize a m (reflect a x)-polarize a q (reflect a x)| ≤
        |m x-q x|+|m (reflect a x)-q (reflect a x)| := by
  -- The preferred-side assertion applies to both functions with exactly the same sorting direction.
  have hl (y : ℝ) (hy : y ≤ a) :
      |polarize a m y-polarize a q y|+
        |polarize a m (reflect a y)-polarize a q (reflect a y)| ≤
          |m y-q y|+|m (reflect a y)-q (reflect a y)| := by
    rw [(polarize_left_pair a m hy).1,(polarize_left_pair a m hy).2,
      (polarize_left_pair a q hy).1,(polarize_left_pair a q hy).2]
    exact sorted_pair_distance _ _ _ _
  by_cases hx : x ≤ a
  · exact hl x hx
  · have hr : reflect a x ≤ a := by dsimp [reflect]; linarith
    have h := hl (reflect a x) hr
    simp only [reflect_reflect] at h
    linarith

/-- Polarization is nonexpansive for the actual real L1 distance.
Use: extends the limiting rearrangement construction from regular densities to general L1 densities.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the reflected-pair contraction. Reflection preserves the two
L1 integrals, so the common factor two cancels. -/
theorem polarize_l1_distance {m q : ℝ → ℝ} (hm : Measurable m) (hq : Measurable q)
    (him : Integrable m) (hiq : Integrable q) (a : ℝ) :
    (∫ x, |polarize a m x-polarize a q x|) ≤ ∫ x, |m x-q x| := by
  -- All four integrals are justified before averaging over the reflection pair.
  have hpm : Integrable (polarize a m) := polarize_integrable_comp hm measurable_id him a
  have hpq : Integrable (polarize a q) := polarize_integrable_comp hq measurable_id hiq a
  have hi := (hpm.sub hpq).abs
  have ho := (him.sub hiq).abs
  have h := integral_mono (hi.add (hi.comp_sub_left (2*a)))
    (ho.add (ho.comp_sub_left (2*a))) (fun x => polarize_distance_pair a m q x)
  have hpi := integral_add hi (hi.comp_sub_left (2*a))
  have hoi := integral_add ho (ho.comp_sub_left (2*a))
  simp only [Pi.add_apply,Pi.sub_apply] at h hpi hoi
  rw [hpi,hoi,integral_sub_left_eq_self (fun x => |polarize a m x-polarize a q x|) volume (2*a),
    integral_sub_left_eq_self (fun x => |m x-q x|) volume (2*a)] at h
  linarith

/-- Two-point polarization is nonexpansive for uniform absolute error.
Use: closure of polarization-invariant families under uniform approximation.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the same maximum or minimum is used in both functions; finite real order
cases bound its difference by the common bound on the two original differences. -/
theorem polarize_uniform_distance {m q : ℝ → ℝ} {δ : ℝ}
    (h : ∀ x, |m x-q x| ≤ δ) (a x : ℝ) :
    |polarize a m x-polarize a q x| ≤ δ := by
  -- Only the original point and its reflection enter the same sorting operation.
  have hx := h x
  have hy := h (reflect a x)
  unfold polarize
  split_ifs <;> grind [abs_eq_max_neg]

/-- Reflection is an isometry of the actual real line.
Use: preserves the Lipschitz constant of the reflected density before sorting.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: reflection negates each difference, preserving its absolute value. -/
theorem reflect_isometry (a : ℝ) : Isometry (reflect a) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [Real.dist_eq,Real.dist_eq,
    show reflect a x-reflect a y=-(x-y) by dsimp [reflect]; ring,abs_neg]

/-- Polarization preserves the exact Lipschitz constant, including across its sorting boundary.
Use: compactness of regular polarization orbits in the symmetric rearrangement construction.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: maximum and minimum of the two reflected Lipschitz functions keep their
constant. On opposite sides of a, both branches agree at a; add their two
distance estimates and use additivity of the real segment lengths. -/
theorem polarize_lipschitz {m : ℝ → ℝ} {K : ℝ≥0} (hm : LipschitzWith K m) (a : ℝ) :
    LipschitzWith K (polarize a m) := by
  -- The two globally Lipschitz branches have exactly the same value at the reflection boundary.
  have hr : LipschitzWith K (fun x => m (reflect a x)) := by
    simpa only [mul_one,Function.comp_def] using hm.comp (reflect_isometry a).lipschitzWith
  have hf : LipschitzWith K (fun x => max (m x) (m (reflect a x))) := by
    simpa only [max_self] using hm.max hr
  have hg : LipschitzWith K (fun x => min (m x) (m (reflect a x))) := by
    simpa only [max_self] using hm.min hr
  have ha : reflect a a=a := by dsimp [reflect]; ring
  have hcross (x y : ℝ) (hx : x ≤ a) (hy : a < y) :
      dist (polarize a m x) (polarize a m y) ≤ (K : ℝ)*dist x y := by
    have h1 := hf.dist_le_mul x a
    have h2 := hg.dist_le_mul a y
    simp only [ha,max_self] at h1
    simp only [ha,min_self] at h2
    rw [polarize,ite_eq_left hx,polarize,ite_eq_right (not_le.mpr hy)]
    calc
      _ ≤ dist (max (m x) (m (reflect a x))) (m a)+
          dist (m a) (min (m y) (m (reflect a y))) := dist_triangle _ _ _
      _ ≤ (K : ℝ)*dist x a+(K : ℝ)*dist a y := add_le_add h1 h2
      _ = (K : ℝ)*dist x y := by
        rw [← mul_add]
        congr 1
        rw [Real.dist_eq,Real.dist_eq,Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hx),abs_of_nonpos (sub_nonpos.mpr hy.le),
          abs_of_nonpos (sub_nonpos.mpr (hx.trans hy.le))]
        ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ≤ a
  · by_cases hy : y ≤ a
    · simpa only [polarize,ite_eq_left hx,ite_eq_left hy] using hf.dist_le_mul x y
    · exact hcross x y hx (not_le.mp hy)
  · by_cases hy : y ≤ a
    · simpa only [dist_comm] using hcross y x hy (not_le.mp hx)
    · simpa only [polarize,ite_eq_right hx,ite_eq_right hy] using hg.dist_le_mul x y

end
end jacobi.Rearrangement
