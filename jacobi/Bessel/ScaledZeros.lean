import jacobi.Bessel.ScaledWave

/-!
Article: jacobi, Proposition B.1.
Every scaled comparison zero is identified with j_(alpha,k)/D, in its
actual canonical order. First-zero and successor minimality, and all
zero-free original nodal intervals, follow from the proved complete Bessel
zero enumeration. No asymptotic numbering is used.
Use: the numbered Sturm theorem compares these actual j_(alpha,k)/D against the actual finite Jacobi angles.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The genuine canonical Bessel zero list in positive-frequency comparison coordinates.
Use: the numbered Sturm theorem compares these actual j_(alpha,k)/D against the actual finite Jacobi angles.
Article: jacobi, Proposition B.1.
-/
def scaledZero (a : ℝ) (ha : -1<a) (D : ℝ) (k : ℕ) : ℝ := positiveZero a ha k/D

/-- Every actual positive-frequency scaled Bessel zero is strictly positive.
Use: the source nodal intervals lie in the genuine positive-axis comparison domain.
Article: jacobi, Proposition B.1.
Proof: the original positive Bessel zero is divided by the strictly positive actual frequency. -/
theorem scaledZero_pos {a D : ℝ} (ha : -1<a) (hD : 0<D) (k : ℕ) : 0<scaledZero a ha D k :=
  div_pos (positiveZero_properties ha k).1 hD

/-- The actual scaled Bessel zero list is strictly increasing.
Use: retains the canonical source numbering under comparison frequency scaling.
Article: jacobi, Proposition B.1.
Proof: divide the original strictly increasing positive Bessel zero list by the same positive actual frequency. -/
theorem scaledZero_strictMono {a D : ℝ} (ha : -1<a) (hD : 0<D) : StrictMono (scaledZero a ha D) := by
  intro i j hij
  exact div_lt_div_of_pos_right (positiveZero_strictMono ha hij) hD

/-- Every actual scaled source zero is a zero of the original normalized comparison wave.
Use: gives the actual left nodal endpoints in reverse numbered Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: undo the positive scaling and use the original cylindrical Bessel zero and its already proved exact entire-function normalization. -/
theorem scaledZero_is_zero {a D : ℝ} (ha : -1<a) (hD : 0<D) (k : ℕ) :
    scaledWave a D (scaledZero a ha D k)=0 := by
  rw [scaledWave_zero_iff a hD (scaledZero_pos ha hD k)]
  have he : D*scaledZero a ha D k=positiveZero a ha k := by
    unfold scaledZero
    field_simp [hD.ne']
  rw [he]
  exact (cylindrical_zero_iff ha (positiveZero_properties ha k).1).mp (positiveZero_is_zero ha k)

/-- The original first scaled Bessel zero is no larger than any positive actual zero of the comparison wave.
Use: discharges the actual first-index minimality in forward numbered Jacobi/Bessel comparison.
Article: jacobi, Proposition B.1.
Proof: exhaust the original wave zero by a canonical Bessel index and use monotonicity from index zero before undoing the positive scale. -/
theorem scaledZero_first_le {a D x : ℝ} (ha : -1<a) (hD : 0<D) (hx : 0<x)
    (hz : scaledWave a D x=0) : scaledZero a ha D 0≤x := by
  obtain ⟨i,hi⟩ := scaledWave_zero_index ha hD hx hz
  apply (div_le_iff₀ hD).mpr
  have hm := (positiveZero_strictMono ha).monotone (Nat.zero_le i)
  rw [hi] at hm
  nlinarith

/-- Every original comparison-wave zero after a scaled Bessel zero lies at or beyond the true next canonical scaled zero.
Use: advances forward numbered Sturm comparison without assuming an asymptotic phase index.
Article: jacobi, Proposition B.1.
Proof: exhaustive genuine zero enumeration gives an actual index. Any
index no larger than k contradicts the strict zero ordering. Monotonicity
from k+1 and the positive frequency then give the original successor bound. -/
theorem scaledZero_successor_le {a D x : ℝ} (ha : -1<a) (hD : 0<D) (hx : 0<x)
    (hz : scaledWave a D x=0) (k : ℕ) (hlt : scaledZero a ha D k<x) :
    scaledZero a ha D (k+1)≤x := by
  -- Source indexing is obtained from the actual zero, before applying any order comparison.
  obtain ⟨i,hi⟩ := scaledWave_zero_index ha hD hx hz
  have hki : k< i := by
    by_contra hn
    have hm := (scaledZero_strictMono ha hD).monotone (not_lt.mp hn)
    have he : scaledZero a ha D i=x := by
      unfold scaledZero
      rw [hi,mul_div_cancel_left₀ _ hD.ne']
    rw [he] at hm
    linarith
  apply (div_le_iff₀ hD).mpr
  have hm := (positiveZero_strictMono ha).monotone (show k+1≤ i from hki)
  rw [hi] at hm
  nlinarith

/-- The original scaled Bessel wave is zero-free before its actual first canonical zero.
Use: gives the first genuine original nodal interval in reverse singular Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: any such original zero would contradict the proved first-zero minimality. -/
theorem scaledWave_no_zero_before {a D x : ℝ} (ha : -1<a) (hD : 0<D)
    (hx : x∈Ioo 0 (scaledZero a ha D 0)) : scaledWave a D x≠0 := by
  intro hz
  exact not_lt_of_ge (scaledZero_first_le ha hD hx.1 hz) hx.2

/-- The original scaled Bessel wave is zero-free between every pair of actual consecutive canonical zeros.
Use: supplies all genuine original nodal intervals in reverse numbered Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: successor minimality excludes any actual zero strictly inside this source nodal interval. -/
theorem scaledWave_no_zero_between {a D x : ℝ} (ha : -1<a) (hD : 0<D) (k : ℕ)
    (hx : x∈Ioo (scaledZero a ha D k) (scaledZero a ha D (k+1))) : scaledWave a D x≠0 := by
  intro hz
  exact not_lt_of_ge (scaledZero_successor_le ha hD
    ((scaledZero_pos ha hD k).trans hx.1) hz k hx.1) hx.2

end
end jacobi.Bessel
