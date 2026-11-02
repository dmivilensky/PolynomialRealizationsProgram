import jacobi.Bessel.UniformNodalGap
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: jacobi, Lemma E.1.
Use: the original holomorphic complex-disk branches agree with j_(alpha,k) for every real admissible order, without an assumed continuity theorem for the entire numbered list.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- An actual Bessel-zero sequence in all consecutive sufficiently large quarter-grid disks has exactly the original canonical zero numbering.
Use: the original holomorphic complex-disk branches agree with j_(alpha,k) for every real admissible order, without an assumed continuity theorem for the entire numbered list.
Article: jacobi, Lemma E.1.
Proof: enumerate each actual positive root. The genuine grid separation makes these indices strictly increase; the actual two-nodal-interval lower bound rules out skipping an index between adjacent grid disks. Thus the index is one fixed integer offset plus the grid index. The independently proved numbered Weyl phase forces that offset to vanish. -/
theorem grid_tail_numbering {a : ℝ} (ha : -1<a) (N : ℕ) (w : ℕ → ℝ)
    (hzero : ∀ n : ℕ,∃ m : ℕ,w n=positiveZero a ha m)
    (hclose : ∀ n : ℕ,|w n-phaseGrid a (N+n)|≤1/4)
    (hfar : ∀ n : ℕ,2*(a^2+1)≤w n) :
    ∀ n : ℕ,w n=positiveZero a ha (N+n) := by
  -- The original zero enumeration fixes each constructed root's actual index before any asymptotic comparison.
  choose m hm using hzero
  have hstep (n : ℕ) : m (n+1)=m n+1 := by
    have hc0 := abs_le.mp (hclose n)
    have hc1 := abs_le.mp (hclose (n+1))
    have hgrid : phaseGrid a (N+(n+1))=phaseGrid a (N+n)+Real.pi := by
      unfold phaseGrid
      push_cast
      ring
    have hw : w n<w (n+1) := by rw [hgrid] at hc1; linarith [Real.pi_gt_three]
    have hsep : w (n+1)-w n≤Real.pi+1/2 := by rw [hgrid] at hc1; linarith
    have hmono : m n<m (n+1) := (positiveZero_strictMono ha).lt_iff_lt.mp (by simpa only [← hm n,← hm (n+1)] using hw)
    by_contra hnot
    have hskip : m n+2≤m (n+1) := by omega
    have hgap := positiveZero_twoStep_gap ha (m n) (by rw [← hm n]; exact hfar n)
    have hle := (positiveZero_strictMono ha).monotone hskip
    rw [← hm (n+1)] at hle
    rw [← hm n] at hgap
    nlinarith [Real.pi_gt_three]
  have hmform (n : ℕ) : m n=m 0+n := by
    induction n with
    | zero => omega
    | succ n ih => rw [hstep,ih]; omega
  have hindex : Tendsto (fun n : ℕ => m 0+n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat (m 0)
  have hlimit := (positiveZero_phase_tendsto ha).comp hindex
  have hgrid (n : ℕ) : phaseGrid a (m 0+n)-phaseGrid a (N+n)=((m 0:ℝ)-(N:ℝ))*Real.pi := by
    unfold phaseGrid
    push_cast
    ring
  have hshift : Tendsto (fun n : ℕ => w n-phaseGrid a (N+n)) atTop
      (𝓝 (((m 0:ℝ)-(N:ℝ))*Real.pi)) := by
    convert! hlimit.add_const (((m 0:ℝ)-(N:ℝ))*Real.pi) using 1
    · ext n
      dsimp only [Function.comp_def]
      rw [hm n,hmform n]
      linear_combination hgrid n
    · simp only [zero_add]
  have hbound := le_of_tendsto hshift.abs (Eventually.of_forall hclose)
  have hm0 : m 0=N := by
    have hb := abs_le.mp hbound
    rcases lt_trichotomy (m 0) N with hlt | heq | hgt
    · have hn : (m 0:ℝ)+1≤(N:ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hlt
      nlinarith [Real.pi_gt_three]
    · exact heq
    · have hn : (N:ℝ)+1≤(m 0:ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hgt
      nlinarith [Real.pi_gt_three]
  intro n
  rw [hm n,hmform,hm0]

end
end jacobi.Bessel
