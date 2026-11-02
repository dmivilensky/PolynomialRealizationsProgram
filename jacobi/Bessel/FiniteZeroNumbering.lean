import jacobi.Bessel.Enumeration

/-!
Article: jacobi, Lemma E.1.
Use: finite holomorphic branches retain the article's original numbering after compact zero-free gap exclusion.
-/
namespace jacobi.Bessel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A genuine finite ordered zero family exhausting the original spectral zeros below its common upper threshold is exactly the canonical Bessel prefix.
Use: finite holomorphic branches retain the article's original numbering after compact zero-free gap exclusion.
Article: jacobi, Lemma E.1.
Proof: the genuine least-zero property identifies the first branch. Inductively the true least successor lies below the next branch; completeness places it on some branch, and strict ordering excludes every earlier branch. Thus both inequalities give the original next numbered zero. -/
theorem finite_zero_numbering {a : ℝ} (ha : -1<a) {N : ℕ} (w : Fin N → ℝ) {T : ℝ}
    (hz : ∀ i,w i∈spectralZeros a) (hmono : StrictMono w) (hbelow : ∀ i,w i<T)
    (hcover : ∀ x∈spectralZeros a,x<T → ∃ i,w i=x) :
    ∀ i : Fin N,w i=sigma a ha i := by
  -- All candidate roots belong to the same original spectral zero set and its genuine least-successor enumeration.
  have he (k : ℕ) : ∀ hk : k<N,w ⟨k,hk⟩=sigma a ha k := by
    induction k with
    | zero =>
      intro hk
      have hle := (sigma_first ha).2 (hz ⟨0,hk⟩)
      obtain ⟨j,hj⟩ := hcover _ (sigma_mem ha 0) (hle.trans_lt (hbelow ⟨0,hk⟩))
      have hge := hmono.monotone (show (⟨0,hk⟩:Fin N)≤j from Nat.zero_le _)
      rw [hj] at hge
      exact le_antisymm hge hle
    | succ k ih =>
      intro hk
      have hkp : k<N := by omega
      have hprev := ih hkp
      have hstrict : sigma a ha k<w ⟨k+1,hk⟩ := by
        rw [← hprev]
        exact hmono (by simp)
      have hle := (sigma_successor ha k).2 ⟨hz ⟨k+1,hk⟩,hstrict⟩
      obtain ⟨j,hj⟩ := hcover _ (sigma_mem ha (k+1)) (hle.trans_lt (hbelow ⟨k+1,hk⟩))
      have hjk : k+1≤j.val := by
        by_contra hn
        have hh := hmono.monotone (show j≤(⟨k,hkp⟩:Fin N) from by change j.val≤k; omega)
        rw [hj,hprev] at hh
        exact (not_le_of_gt (sigma_strictMono ha (Nat.lt_succ_self k))) hh
      have hge := hmono.monotone (show (⟨k+1,hk⟩:Fin N)≤j from hjk)
      rw [hj] at hge
      exact le_antisymm hge hle
  intro i
  exact he i.val i.isLt

end
end jacobi.Bessel
