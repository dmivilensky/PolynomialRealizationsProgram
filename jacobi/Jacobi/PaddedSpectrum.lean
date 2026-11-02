import jacobi.Jacobi.OrderedZeroLimit
import jacobi.Jacobi.FiniteMoments
import jacobi.Bessel.EdgeSequence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Article: jacobi, Lemma 1.3.
The exact finite source spectrum is extended by zero to the natural
numbers. It converges coordinatewise to the actual Bessel spectrum and
has a uniform first-trace bound and the consequent C/(k+1) bound.
Source: actual ordered zero convergence and the genuine finite trace formula.
Use: all finite spectra and the genuine infinite Bessel spectrum now share the same index type.
-/
namespace jacobi.Jacobi
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal source scaled resolvent sequence, padded by zero outside its finite degree.
Use: all finite spectra and the genuine infinite Bessel spectrum now share the same index type.
Article: jacobi, Theorem 2.1.
-/
def finiteLambdaAt (a b : ℝ) (ha : -1<a) (hb : -1<b) (n k : ℕ) : ℝ :=
  2/finiteSigmaAt a b ha hb n k

/-- At a valid finite index, the padded spectrum is exactly the actual source resolvent value.
Use: finite trace identities apply to the zero-padded sequence with no spectral redefinition.
Article: jacobi, Theorem 2.1.
Proof: use the proved exact finite squared-zero value and the literal reciprocal definition. -/
theorem finiteLambdaAt_eq {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    finiteLambdaAt a b ha hb n k=finiteLambda a b ha hb n ⟨k,hk⟩ := by
  rw [finiteLambdaAt,finiteSigmaAt_eq ha hb hk,finiteLambda]

/-- The padded spectrum is zero outside the actual finite index set.
Use: proves its genuine finite support and exact sums of every zero-preserving spectral observable.
Article: jacobi, Lemma 1.3.
Proof: outside the degree the squared-zero padding is zero and its totalized reciprocal is zero. -/
theorem finiteLambdaAt_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : n≤k) :
    finiteLambdaAt a b ha hb n k=0 := by
  simp only [finiteLambdaAt,finiteSigmaAt,dite_eq_right (not_lt.mpr hk),div_zero]

/-- The actual padded finite spectrum is nonnegative everywhere.
Use: trace bounds and the dominated limiting spectral arguments use genuine nonnegative summands.
Article: jacobi, Lemma 1.3.
Proof: valid indices have positive actual squared zeros; all other entries are exactly zero. -/
theorem finiteLambdaAt_nonneg {a b : ℝ} (ha : -1<a) (hb : -1<b) (n k : ℕ) :
    0≤finiteLambdaAt a b ha hb n k := by
  by_cases hk : k<n
  · rw [finiteLambdaAt_eq ha hb hk,finiteLambda]
    exact div_nonneg (by norm_num) ((finiteSigma_properties ha hb (by omega)).1 _).le
  · rw [finiteLambdaAt_zero ha hb (not_lt.mp hk)]

/-- The entire padded actual finite spectrum is decreasing, including its terminal transition to zero.
Use: the first trace bounds every indexed value by a uniform inverse-index majorant.
Article: jacobi, Lemma 1.3.
Proof: within the finite range positive squared zeros increase, so their
reciprocals decrease. Beyond the degree the later entry is zero and the earlier entry is nonnegative. -/
theorem finiteLambdaAt_antitone {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    Antitone (finiteLambdaAt a b ha hb n) := by
  -- The terminal transition uses genuine nonnegativity; within the finite range strict positive reciprocals reverse the actual zero order.
  intro i j hij
  by_cases hj : j<n
  · have hi : i<n := lt_of_le_of_lt hij hj
    rw [finiteLambdaAt_eq ha hb hi,finiteLambdaAt_eq ha hb hj,finiteLambda,finiteLambda]
    exact div_le_div_of_nonneg_left (by norm_num)
      ((finiteSigma_properties ha hb (by omega)).1 _)
      ((finiteSigma_properties ha hb (by omega)).2.monotone hij)
  · rw [finiteLambdaAt_zero ha hb (not_lt.mp hj)]
    exact finiteLambdaAt_nonneg ha hb n i

/-- Any zero-preserving spectral observable of the actual padded finite spectrum has exactly its original finite sum.
Use: first traces, second traces and resolvent observations are genuine infinite sums with finite support.
Article: jacobi, Lemma 1.3.
Proof: all terms outside range(n) vanish. The community finite-index
sum identity then identifies the remaining natural sum with the actual finite spectrum. -/
theorem finiteLambdaAt_tsum {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (f : ℝ → ℝ) (hf : f 0=0) :
    (∑' k:ℕ,f (finiteLambdaAt a b ha hb n k))=∑ i:Fin n,f (finiteLambda a b ha hb n i) := by
  -- Finite support is proved before using the total infinite sum.
  have he : (∑' k:ℕ,f (finiteLambdaAt a b ha hb n k))=
      ∑ k∈Finset.range n,f (finiteLambdaAt a b ha hb n k) := by
    apply tsum_eq_sum
    intro k hk
    rw [finiteLambdaAt_zero ha hb (by simpa only [Finset.mem_range,not_lt] using hk),hf]
  rw [he,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteLambdaAt_eq ha hb i.isLt]

/-- The actual padded finite spectral sequence is genuinely summable for every degree.
Use: finite trace upper bounds and genuine infinite-sum inequalities are applied only to convergent series.
Article: jacobi, Lemma 1.3.
Proof: the proved zero-padding identity gives finite support, to which the community summability theorem applies. -/
theorem finiteLambdaAt_summable {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    Summable (finiteLambdaAt a b ha hb n) := by
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro k hk
  exact finiteLambdaAt_zero ha hb (by simpa only [Finset.mem_range,not_lt] using hk)

/-- Every fixed padded actual finite resolvent entry converges to the corresponding actual Bessel edge value.
Use: the pointwise input to the full spectral trace and L1 transfer arguments.
Article: jacobi, Lemma 1.3.
Proof: apply the continuous positive reciprocal map to the proved
canonically indexed squared-zero limit. Its actual limiting zero is strictly positive. -/
theorem finiteLambdaAt_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n : ℕ => finiteLambdaAt a b ha hb n k) atTop
      (𝓝 (jacobi.Bessel.edgeValue a ha k)) := by
  have hp := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  exact tendsto_const_nhds.div (finiteSigmaAt_tendsto ha hb k) hp.ne'

/-- A fixed explicit upper bound for all actual positive-degree finite Jacobi masses.
Use: supplies a uniform inverse-index spectral majorant for all dominated limiting arguments.
Article: jacobi, Lemma 1.3.
-/
def traceBound (a b : ℝ) : ℝ := (1+|a+b+1|)/(2*(a+1))

/-- The actual finite Jacobi first trace is bounded uniformly in positive degree.
Use: controls every finite spectral tail without assuming the infinite first Rayleigh sum.
Article: jacobi, Lemma 1.3.
Proof: the genuine exact mass formula has inverse-degree correction
(alpha+beta+1)/n, bounded above by its absolute numerator for n>=1. -/
theorem finiteLambdaAt_trace_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    (∑' k,finiteLambdaAt a b ha hb n k)≤traceBound a b := by
  have he := finiteLambdaAt_tsum ha hb n id rfl
  simp only [id_eq] at he
  rw [he,finiteLambda_sum ha hb hn]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hf : (a+b+1)/(n:ℝ)≤|a+b+1| := (div_le_iff₀ hnR).mpr
    ((le_abs_self _).trans (by nlinarith [abs_nonneg (a+b+1)]))
  exact div_le_div_of_nonneg_right (by linarith) (by linarith : 0≤2*(a+1))

/-- A single inverse-index bound controls every actual finite scaled Jacobi eigenvalue.
Use: squares and resolvent remainders have summable inverse-square majorants independent of finite degree.
Article: jacobi, Lemma 1.3.
Proof: every earlier entry is at least the kth entry, so the first k+1
entries sum to at least (k+1)*r_(n,k). Their sum is no greater than the
genuine total finite trace. Divide by the positive integer k+1. -/
theorem finiteLambdaAt_index_bound {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (k : ℕ) :
    finiteLambdaAt a b ha hb n k≤traceBound a b/(k+1:ℝ) := by
  -- The lower partial-sum comparison uses the actual padded spectral order, including zero entries.
  have hlow : (k+1:ℝ)*finiteLambdaAt a b ha hb n k≤
      ∑ j∈Finset.range (k+1),finiteLambdaAt a b ha hb n j := by
    calc
      _ = ∑ j∈Finset.range (k+1),finiteLambdaAt a b ha hb n k := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => finiteLambdaAt_antitone ha hb n (by
        have hh : j<k+1 := Finset.mem_range.mp hj
        omega))
  have hupper := (finiteLambdaAt_summable ha hb n).sum_le_tsum (Finset.range (k+1))
    (fun j _ => finiteLambdaAt_nonneg ha hb n j)
  apply (le_div_iff₀ (show (0:ℝ)<k+1 by positivity)).mpr
  nlinarith [hlow.trans (hupper.trans (finiteLambdaAt_trace_bound ha hb hn))]

end
end jacobi.Jacobi
