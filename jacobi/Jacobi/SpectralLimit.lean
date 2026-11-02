import jacobi.Bessel.Rayleigh

/-!
Article: jacobi, Lemma 1.3.
Coordinatewise convergence and the exact first Rayleigh sum imply convergence
of the entire zero-padded Jacobi resolvent spectrum in L1. The argument uses
the discrete Scheffe identity and genuinely summable positive spectral tails.
Use: the actual first Rayleigh sum rules out loss of mass in the full Jacobi to Bessel spectral limit.
-/
namespace jacobi.Jacobi
noncomputable section
open Filter
open scoped Topology

/-- Discrete Scheffe convergence for nonnegative summable sequences.
Use: the actual first Rayleigh sum rules out loss of mass in the full Jacobi to Bessel spectral limit.
Article: jacobi, Lemma 1.3.
Source: Scheffe's lemma for counting measure, proved here directly by dominated convergence.
Proof: the deficits max(g-f,0) are dominated by the summable limiting sequence.
Their total tends to zero. The scalar absolute-value identity expresses the
L1 distance as the mass difference plus twice this vanishing deficit. -/
theorem nonnegative_scheffe {f : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (hf : ∀ n, Summable (f n)) (hg : Summable g)
    (hfn : ∀ n k, 0 ≤ f n k) (hgn : ∀ k, 0 ≤ g k)
    (hp : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k)))
    (hm : Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k))) :
    Tendsto (fun n => ∑' k, |f n k-g k|) atTop (𝓝 0) := by
  -- Only the limiting spectrum dominates the deficits; no uniform summable bound for the finite spectra is assumed.
  have hb : ∀ n k, max (g k-f n k) 0 ≤ g k :=
    fun n k => max_le (sub_le_self _ (hfn n k)) (hgn k)
  have hd : ∀ n, Summable (fun k => max (g k-f n k) 0) :=
    fun n => hg.of_nonneg_of_le (fun k => le_max_right _ _) (hb n)
  have ht := tendsto_tsum_of_dominated_convergence hg
    (fun k => by simpa using ((tendsto_const_nhds (x := g k)).sub (hp k)).max (tendsto_const_nhds (x := (0:ℝ))))
    (Filter.Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
      exact hb n k))
  simp only [tsum_zero] at ht
  have he : ∀ n, (∑' k, |f n k-g k|)=(∑' k,f n k)-(∑' k,g k)+2*(∑' k,max (g k-f n k) 0) := by
    intro n
    rw [← (hf n).tsum_sub hg,← tsum_mul_left,← ((hf n).sub hg).tsum_add ((hd n).mul_left 2)]
    apply tsum_congr
    intro k
    by_cases hk : f n k ≤ g k
    · rw [abs_of_nonpos (sub_nonpos.mpr hk),max_eq_left (sub_nonneg.mpr hk)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hk)),max_eq_right (sub_nonpos.mpr (le_of_not_ge hk))]
      ring
  simp_rw [he]
  simpa using (hm.sub (tendsto_const_nhds (x := ∑' k,g k))).add (ht.const_mul 2)

/-- The entire actual zero-padded Jacobi spectrum converges in L1 to the genuine Bessel edge spectrum.
Use: transfers every Lipschitz spectral observable, the canonical product and finite-fibre limits without a tail hypothesis.
Article: jacobi, Lemma 1.3.
Proof: the actual finite and infinite spectra are nonnegative and summable.
Their ordered coordinates converge by zero stability and their genuine masses
converge by the exact finite trace and first infinite Rayleigh formulas.
The preceding discrete Scheffe lemma finishes the full tail argument. -/
theorem finiteLambdaAt_l1_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => ∑' k, |finiteLambdaAt a b ha hb n k- jacobi.Bessel.edgeValue a ha k|)
      atTop (𝓝 0) := by
  -- The infinite limiting mass is a proved Bessel theorem, rather than an additional premise.
  apply nonnegative_scheffe (finiteLambdaAt_summable ha hb) (jacobi.Bessel.edgeValue_summable ha)
    (finiteLambdaAt_nonneg ha hb) (fun k => ((jacobi.Bessel.edgeValue_properties ha).1 k).le)
    (finiteLambdaAt_tendsto ha hb)
  have he : (fun n : ℕ => ∑' k,finiteLambdaAt a b ha hb n k)=
      fun n : ℕ => ∑ i : Fin n,finiteLambda a b ha hb n i := by
    funext n
    exact finiteLambdaAt_tsum ha hb n id rfl
  rw [he,jacobi.Bessel.first_rayleigh_sum ha]
  exact finiteLambda_sum_tendsto ha hb

end
end jacobi.Jacobi
