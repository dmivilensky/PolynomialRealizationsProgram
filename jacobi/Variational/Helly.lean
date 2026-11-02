import jacobi.Variational.Tails
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Monotone

/-!
Article: jacobi, Lemma D.1.
Helly selection for nonnegative antitone functions with pointwise bounds.
The proof selects limits on the countable rational set, constructs the
right-hand monotone envelope, and squeezes at every continuity point.
One further selection on the countable jump set gives convergence everywhere.
Source: Helly's selection theorem; the selection argument is proved here from
mathlib's Tychonoff theorem and sequential compactness of countable products.
Use: extracts the a.e. limit of rearranged minimizing sequences after logarithmic change of the spatial variable; the limit's discontinuities are countable.
-/
namespace jacobi.Variational
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Helly selection under pointwise bounds, without an assumed convergent subsequence.
Use: extracts the a.e. limit of rearranged minimizing sequences after logarithmic
change of the spatial variable; the limit's discontinuities are countable.
Article: jacobi, Lemma D.1.
Source: Helly's selection theorem for monotone functions.
Proof: compactness on rational coordinates supplies a common subsequence;
the supremum of future rational limits is antitone, and nearby rational
coordinates squeeze the subsequence at all continuity points. -/
theorem helly_continuity_subsequence (f : ℕ → ℝ → ℝ) (hf : ∀ n, Antitone (f n))
    (hn : ∀ n x, 0 ≤ f n x) (C : ℚ → ℝ) (hC : ∀ n (r : ℚ), f n r ≤ C r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      Antitone g ∧ (∀ x, 0 ≤ g x) ∧
        ∀ x, ContinuousAt g x → Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  -- A countable product of compact intervals gives one subsequence for all rational points.
  have hc : IsCompact {a : ℚ → ℝ | ∀ r, a r ∈ Icc 0 (C r)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨a,ha,φ,hφ,hl⟩ := hc.tendsto_subseq (x := fun n (r : ℚ) => f n r)
    (fun n r => ⟨hn n r,hC n r⟩)
  have hr (r : ℚ) : Tendsto (fun n => f (φ n) r) atTop (𝓝 (a r)) :=
    tendsto_pi_nhds.mp hl r
  have ha0 (r : ℚ) : 0 ≤ a r := (ha r).1
  have haanti : Antitone a := by
    intro r s hrs
    exact le_of_tendsto_of_tendsto (hr s) (hr r)
      (Filter.Eventually.of_forall fun n => hf (φ n) (by exact_mod_cast hrs))
  -- Future rational limits have a finite supremum: any rational to the left bounds them all.
  let A (x : ℝ) : Set ℝ := a '' {r : ℚ | x < (r : ℝ)}
  have hne (x : ℝ) : (A x).Nonempty := by
    obtain ⟨r,hrx⟩ := exists_rat_gt x
    exact ⟨a r,⟨r,hrx,rfl⟩⟩
  have hbd (x : ℝ) : BddAbove (A x) := by
    obtain ⟨r,hrx⟩ := exists_rat_lt x
    refine ⟨a r,?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact haanti (by exact_mod_cast (hrx.trans hs).le)
  let g (x : ℝ) := sSup (A x)
  have hga (x : ℝ) (r : ℚ) (hxr : x < (r : ℝ)) : a r ≤ g x :=
    le_csSup (hbd x) ⟨r,hxr,rfl⟩
  have hag (x : ℝ) (r : ℚ) (hrx : (r : ℝ) < x) : g x ≤ a r := by
    apply csSup_le (hne x)
    rintro y ⟨s,hs,rfl⟩
    exact haanti (by exact_mod_cast (hrx.trans hs).le)
  have hganti : Antitone g := by
    intro x y hxy
    apply csSup_le (hne y)
    rintro z ⟨r,hrx,rfl⟩
    exact hga x r (hxy.trans_lt hrx)
  have hg0 (x : ℝ) : 0 ≤ g x := by
    obtain ⟨r,hrx⟩ := exists_rat_gt x
    exact (ha0 r).trans (hga x r hrx)
  refine ⟨φ,hφ,g,hganti,hg0,?_⟩
  -- Continuity of the envelope closes the gap between left and right rational bounds.
  intro x hx
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hx (ε/2) (by positivity)
  obtain ⟨r,hur,hrx⟩ := exists_rat_btwn (show x-δ/2 < x by linarith)
  obtain ⟨s,hxs,hsv⟩ := exists_rat_btwn (show x < x+δ/2 by linarith)
  have hu : |g (x-δ/2)-g x| < ε/2 := by
    apply hd
    rw [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos (by positivity : 0 < δ/2)]
    linarith
  have hv : |g (x+δ/2)-g x| < ε/2 := by
    apply hd
    rw [Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity : 0 < δ/2)]
    linarith
  have hrupper := hga (x-δ/2) r hur
  have hslower := hag (x+δ/2) s hsv
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hr r) (ε/2) (by positivity)
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp (hr s) (ε/2) (by positivity)
  refine ⟨max N K,fun n hnk => ?_⟩
  have hrn : |f (φ n) r-a r| < ε/2 := by
    simpa only [Real.dist_eq] using hN n (le_of_max_le_left hnk)
  have hsn : |f (φ n) s-a s| < ε/2 := by
    simpa only [Real.dist_eq] using hK n (le_of_max_le_right hnk)
  have hfx := hf (φ n) hrx.le
  have hxf := hf (φ n) hxs.le
  rw [Real.dist_eq,abs_lt]
  exact ⟨by linarith [(abs_lt.mp hsn).1,(abs_lt.mp hv).1],
    by linarith [(abs_lt.mp hrn).2,(abs_lt.mp hu).2]⟩

/-- Full pointwise Helly selection, including the countably many jump points.
Use: discharges the article's convergence claim at every nonzero spatial point,
rather than supplying only almost-everywhere convergence as an extra premise.
Article: jacobi, Lemma D.1.
Source: Helly's selection theorem for monotone functions.
Proof: first select convergence at continuity points, then use compactness on
the countable set of remaining discontinuities; pointwise limits preserve order. -/
theorem helly_antitone (f : ℕ → ℝ → ℝ) (hf : ∀ n, Antitone (f n))
    (hn : ∀ n x, 0 ≤ f n x) (C : ℚ → ℝ) (hC : ∀ n (r : ℚ), f n r ≤ C r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      Antitone g ∧ (∀ x, 0 ≤ g x) ∧
        ∀ x, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  classical
  -- Continuity points already share a subsequence, leaving only countably many jumps.
  obtain ⟨φ,hφ,g,hg,_,hlim⟩ := helly_continuity_subsequence f hf hn C hC
  let D := {x : ℝ // ¬ContinuousAt g x}
  let : Countable D := hg.countable_not_continuousAt.to_subtype
  choose r hr using fun x : ℝ => exists_rat_lt x
  have hc : IsCompact {a : D → ℝ | ∀ x : D, a x ∈ Icc 0 (C (r x))} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨a,_,ψ,hψ,hψlim⟩ := hc.tendsto_subseq (x := fun n (x : D) => f (φ n) x)
    (fun n x => ⟨hn _ _,(hf _ (hr x).le).trans (hC _ _)⟩)
  -- Fill each jump with its own subsequential limit; continuity-point limits stay unchanged.
  let q (x : ℝ) := if hx : ContinuousAt g x then g x else a ⟨x,hx⟩
  have hq (x : ℝ) : Tendsto (fun n => f (φ (ψ n)) x) atTop (𝓝 (q x)) := by
    by_cases hx : ContinuousAt g x
    · simpa only [q,dite_eq_left hx,Function.comp_def] using (hlim x hx).comp hψ.tendsto_atTop
    · simpa only [q,dite_eq_right hx,Function.comp_def] using tendsto_pi_nhds.mp hψlim (⟨x,hx⟩ : D)
  refine ⟨φ ∘ ψ,hφ.comp hψ,q,?_,?_,hq⟩
  · intro x y hxy
    exact le_of_tendsto_of_tendsto (hq y) (hq x)
      (Filter.Eventually.of_forall fun n => hf _ hxy)
  · intro x
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hq x)
      (Filter.Eventually.of_forall fun n => hn _ x)

end
end jacobi.Variational
