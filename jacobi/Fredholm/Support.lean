import jacobi.Fredholm.StateIntegrals
import jacobi.Fredholm.GreenQuadrature

/-!
Article: jacobi, Theorem D.7.
The actual multiplier endpoint gives full support. Every strict interior
shape has a unique finite positive switching radius, and the density is
positive exactly inside its centered core. These are consequences of the
genuine Green monotonicity and free limit, not prescribed candidate data.
Source: intermediate values, actual normal complementarity and the Euler density.
Use: identifies the true support rather than merely the support of a proposed formula.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual Fredholm density is positive exactly where its genuine Green diagonal exceeds the switching level.
Use: identifies the true support rather than merely the support of a proposed formula.
Article: jacobi, Theorem D.7.
Proof: the actual density identity has a strictly positive amplitude and
coupling; the square of the clipped Green gap is positive exactly when that gap is positive. -/
theorem Optimizer.positive_iff {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (x : ℝ) :
    0<P.density.value x ↔ P.edge<P.g hs.le x := by
  -- Positive coupling and amplitude preserve the exact zero set of the clipped square.
  have hA := (P.parameter_signs hs).2
  have he := P.density_formula hs x
  constructor
  · intro hx
    by_contra! hn
    rw [max_eq_right (sub_nonpos.mpr hn),zero_pow (by decide : 2≠0),mul_zero] at he
    nlinarith [mul_pos hs hx]
  · intro hx
    rw [max_eq_left (sub_pos.mpr hx).le] at he
    have hh := mul_pos (sq_pos_of_pos hA) (sq_pos_of_pos (sub_pos.mpr hx))
    nlinarith

/-- The actual full-support endpoint has a strictly positive density everywhere.
Use: closes the free branch of the source's support dichotomy, including its noncompact tail.
Article: jacobi, Theorem D.7.
Proof: tau=1 is exactly the actual switching value one half, strictly
below the genuine positive-mass Green diagonal at every finite point. -/
theorem Optimizer.full_support {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (ht : P.tau hs=1) (x : ℝ) : 0<P.density.value x := by
  apply (P.positive_iff hs x).mpr
  rw [(P.free_iff hs).1.mp ht]
  exact green_diagonal_strict P.density P.mass_pos hs P.pole x

/-- Every actual strict interior Fredholm optimizer has a unique finite centered positive core and its exact switching boundary.
Use: the interior branch has the source's compact support, with no assumed finite-radius premise.
Article: jacobi, Theorem D.7.
Proof: strict tau<1 puts g_e above one half, while the central turn lies
strictly above g_e. The genuine free-state limit gives a finite crossing.
Strict Green monotonicity and evenness determine the entire core and
also give a strict sub-switching level beyond its boundary. -/
theorem Optimizer.compact_core {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s)
    (ht : P.tau hs<1) :
    ∃ a : ℝ,0<a ∧ P.g hs.le a=P.edge ∧
      (∀ x : ℝ,0<P.density.value x ↔ |x|<a) ∧
      (∀ x : ℝ,a< |x| → P.g hs.le x<P.edge) := by
  -- The crossing is selected from the true inverse diagonal's limit, not a guessed cutoff integral.
  have he0 := (P.parameter_signs hs).1
  have he : (1/2:ℝ)<P.edge := lt_of_le_of_ne he0 (by
    intro hz
    exact ht.ne ((P.free_iff hs).1.mpr hz.symm))
  have h0 := (P.shape hs).1
  have hc := (P.density.greenDiagonal_contDiff P.continuous hs.le P.pole).continuous
  obtain ⟨R,hR,hbelow⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((green_diagonal_limits P.density hs.le P.pole).1.eventually (Iio_mem_nhds he))).exists
  obtain ⟨a,ha,hvalue⟩ := intermediate_value_Icc' hR.le hc.continuousOn ⟨hbelow.le,h0.le⟩
  change P.g hs.le a=P.edge at hvalue
  have hpos : 0<a := lt_of_le_of_ne ha.1 (by
    intro hz
    rw [← hz] at hvalue
    exact h0.ne' hvalue)
  have habs (x : ℝ) : P.g hs.le |x|=P.g hs.le x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      exact (P.shape hs).2.2.1 x
  refine ⟨a,hpos,hvalue,fun x => ?_,fun x hx => ?_⟩
  · rw [P.positive_iff hs x,← habs x]
    constructor
    · intro hx
      by_contra! hn
      have hh := (P.green_strictAnti hs).antitoneOn (mem_Ici.mpr hpos.le)
        (mem_Ici.mpr (abs_nonneg x)) hn
      rw [hvalue] at hh
      linarith
    · intro hx
      have hh := P.green_strictAnti hs (mem_Ici.mpr (abs_nonneg x)) (mem_Ici.mpr hpos.le) hx
      rwa [hvalue] at hh
  · have hh := P.green_strictAnti hs (mem_Ici.mpr hpos.le) (mem_Ici.mpr (abs_nonneg x)) hx
    rwa [hvalue,habs] at hh

end
end jacobi.Fredholm
