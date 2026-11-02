import jacobi.Bessel.ZeroExistence
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
Article: jacobi, Theorem 2.1.
The actual positive Bessel spectral zeros are enumerated in strictly
increasing order. Every zero occurs and the sequence tends to infinity.
The index here starts at zero, so sigma n is the article's sigma_(n+1).
Source: local finiteness, positivity and oscillation proved for the actual entire function.
Use: constructs a genuine least zero and a genuine least successor, excluding omitted accumulation points.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every bounded initial segment of the actual Bessel spectral zero set is finite.
Use: constructs a genuine least zero and a genuine least successor, excluding omitted accumulation points.
Article: jacobi, Theorem 2.1.
Proof: positivity places the initial segment in a compact complex ball.
The actual entire function has finitely many zeros there; the real inclusion is injective. -/
theorem spectralZeros_below_finite {a : ℝ} (ha : -1<a) (R : ℝ) :
    {x∈spectralZeros a | x≤R}.Finite := by
  -- The finiteness comes from the original analytic zero set.
  have hC := normalized_zeros_finite (a := (a:ℂ)) (by simpa using ha)
    (K := Metric.closedBall 0 (max R 0)) (isCompact_closedBall _ _)
  have hpre := hC.preimage Complex.ofReal_injective.injOn
  apply hpre.subset
  intro x hx
  refine ⟨?_,hx.1⟩
  rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (spectralZero_pos ha hx.1)]
  exact hx.2.trans (le_max_left _ _)

/-- Above every real threshold there is a genuine least Bessel spectral zero.
Use: defines both the first zero and every immediate successor in the article's sequence.
Article: jacobi, Theorem 2.1.
Proof: oscillation supplies one upper zero. Minimize within the finite
nonempty segment ending there; every zero outside that segment is larger. -/
theorem spectralZero_least_after {a : ℝ} (ha : -1<a) (B : ℝ) :
    ∃ x,IsLeast {x∈spectralZeros a | B<x} x := by
  -- Finite minimization avoids assuming a discrete zero enumeration.
  obtain ⟨y,hy,hBy⟩ := spectralZero_above ha B
  let S : Set ℝ := {x∈spectralZeros a | x≤y ∧ B<x}
  have hfin : S.Finite := (spectralZeros_below_finite ha y).subset (fun _ hx => ⟨hx.1,hx.2.1⟩)
  have hne : S.Nonempty := ⟨y,hy,le_rfl,hBy⟩
  let x := hfin.isWF.min hne
  have hx : x∈S := hfin.isWF.min_mem hne
  refine ⟨x,⟨hx.1,hx.2.2⟩,?_⟩
  intro z hz
  by_cases hzY : z≤y
  · exact le_of_not_gt (hfin.isWF.not_lt_min hne ⟨hz.1,hzY,hz.2⟩)
  · exact hx.2.1.trans (le_of_not_ge hzY)

/-- The increasing enumeration of all genuine squared Bessel zeros, indexed from zero.
Use: defines the source edge spectrum by actual zeros rather than an assumed list.
Article: jacobi, Theorem 2.1.
-/
def sigma (a : ℝ) (ha : -1<a) : ℕ → ℝ
  | 0 => Classical.choose (spectralZero_least_after ha (-1))
  | n+1 => Classical.choose (spectralZero_least_after ha (sigma a ha n))

/-- The initial enumerated zero is the least actual spectral zero.
Use: proves that the enumeration starts at the first source Bessel zero.
Article: jacobi, Theorem 2.1.
Proof: the defining threshold is minus one, while every actual zero is positive. -/
theorem sigma_first {a : ℝ} (ha : -1<a) : IsLeast (spectralZeros a) (sigma a ha 0) := by
  have h := Classical.choose_spec (spectralZero_least_after ha (-1))
  exact ⟨h.1.1,fun x hx => h.2 ⟨hx,by linarith [spectralZero_pos ha hx]⟩⟩

/-- Every enumerated successor is the least actual zero strictly above its predecessor.
Use: establishes strict ordering and exhaustive coverage without a hidden interlacing premise.
Article: jacobi, Theorem 2.1.
Proof: this is the proved least-successor property used in the recursive definition. -/
theorem sigma_successor {a : ℝ} (ha : -1<a) (n : ℕ) :
    IsLeast {x∈spectralZeros a | sigma a ha n<x} (sigma a ha (n+1)) :=
  Classical.choose_spec (spectralZero_least_after ha (sigma a ha n))

/-- Every term in the Bessel spectral sequence is a genuine zero of the original entire function.
Use: the enumerated source spectrum has no artificial entries.
Article: jacobi, Theorem 2.1.
Proof: the first term and every least successor belong to the actual zero set. -/
theorem sigma_mem {a : ℝ} (ha : -1<a) (n : ℕ) : sigma a ha n∈spectralZeros a := by
  cases n with
  | zero => exact (sigma_first ha).1
  | succ n => exact (sigma_successor ha n).1.1

/-- The actual squared Bessel zero enumeration is strictly increasing.
Use: its ordered reciprocals define the decreasing edge spectrum.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: each least successor is strictly above its predecessor. -/
theorem sigma_strictMono {a : ℝ} (ha : -1<a) : StrictMono (sigma a ha) :=
  strictMono_nat_of_lt_succ (fun n => (sigma_successor ha n).1.2)

/-- The genuine squared Bessel zero sequence is unbounded above.
Use: proves divergence to infinity and allows locating any proposed zero between consecutive terms.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: strict increase makes the range infinite, whereas every bounded
initial segment of the actual zero set was proved finite. -/
theorem sigma_unbounded {a : ℝ} (ha : -1<a) : ¬BddAbove (range (sigma a ha)) := by
  intro hB
  obtain ⟨B,hB⟩ := hB
  have hfin := (spectralZeros_below_finite ha B).subset (show range (sigma a ha)⊆_ from by
    rintro x ⟨n,rfl⟩
    exact ⟨sigma_mem ha n,hB (mem_range_self n)⟩)
  exact (Set.infinite_range_of_injective (sigma_strictMono ha).injective) hfin

/-- The actual squared Bessel zeros tend to positive infinity.
Use: supports spectral tails and the future canonical product over every source zero.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: monotonicity and the proved unbounded range give the genuine filter limit. -/
theorem sigma_tendsto {a : ℝ} (ha : -1<a) : Tendsto (sigma a ha) atTop atTop :=
  tendsto_atTop_atTop_of_monotone' (sigma_strictMono ha).monotone (sigma_unbounded ha)

/-- Every actual Bessel spectral zero occurs in the increasing sequence.
Use: ensures products and sums over the sequence account for the full actual zero set.
Article: jacobi, Theorem 2.1.
Proof: take the first enumerated term at or above the proposed zero.
If it is the first term, first-zero minimality gives equality. Otherwise
the preceding term lies below the zero and least-successor minimality
again forces equality. -/
theorem sigma_exhaustive {a : ℝ} (ha : -1<a) {x : ℝ} (hx : x∈spectralZeros a) :
    ∃ n,sigma a ha n=x := by
  -- Unboundedness provides an upper term; natural-number minimization provides the first one.
  obtain ⟨y,⟨n,rfl⟩,hxy⟩ := not_bddAbove_iff.mp (sigma_unbounded ha) x
  have he : ∃ n,x≤sigma a ha n := ⟨n,hxy.le⟩
  let k := Nat.find he
  have hk : x≤sigma a ha k := Nat.find_spec he
  cases hk0 : k with
  | zero => exact ⟨0,le_antisymm ((sigma_first ha).2 hx) (hk0 ▸ hk)⟩
  | succ m =>
    have hmk : m<k := by omega
    have hm : sigma a ha m<x := lt_of_not_ge (Nat.find_min he hmk)
    refine ⟨m+1,le_antisymm ((sigma_successor ha m).2 ⟨hx,hm⟩) ?_⟩
    simpa only [hk0] using hk

end
end jacobi.Bessel
