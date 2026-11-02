import jacobi.Bessel.Enumeration

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The same elementary ordering argument applies to Jacobi and Laguerre:
positive strictly ordered finite zeros, existence near each limiting
zero, compact gap exclusion and local uniqueness fix every original
finite index. The actual polynomial families discharge these inputs.
Source: stability of ordered simple zeros under locally uniform convergence.
Use: ordered_zero_limit expresses actual fixed-index spectral convergence on all natural degrees.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A complete increasing finite zero list, padded by zero before the requested index exists.
Use: ordered_zero_limit expresses actual fixed-index spectral convergence on all natural degrees.
Article: jacobi, Proposition 6.1.
-/
def finiteZeroAt (Z:(n:ℕ)→Fin n→ℝ) (n k:ℕ) : ℝ :=
  if hk:k < n then Z n ⟨k,hk⟩ else 0

/-- On every existing finite index the padded zero is exactly the original finite zero.
Use: ordered_zero_limit uses the unchanged finite ordering after discarding only a finite degree prefix.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: evaluate the dependent conditional with the genuine finite index bound. -/
theorem finiteZeroAt_eq (Z:(n:ℕ)→Fin n→ℝ) {n k:ℕ} (hk:k < n) :
    finiteZeroAt Z n k=Z n ⟨k,hk⟩ := by rw [finiteZeroAt,dite_eq_left hk]

/-- Positive ordered finite zero lists converge at each original index to the actual complete Bessel zero list once the genuine zero-stability properties hold.
Use: the Laguerre application supplies every premise from its actual polynomial, complex Mehler--Heine limit and positive simple matrix spectrum.
Article: jacobi, Proposition 6.1.
Proof: the first finite root is trapped by compact exclusion below
the first limit and existence near it. Inductively, local injectivity
excludes an extra root near the preceding limit, compact exclusion
clears the intervening gap, and existence near the next limit gives
the upper bound. Both bounds retain the original finite numbering. -/
theorem ordered_zero_limit {a:ℝ} (ha:-1 < a)
    (Z:(n:ℕ)→Fin n→ℝ) (F:ℕ→ℂ→ℂ)
    (hZ:∀n,(∀i:Fin n,0 < Z n i) ∧ StrictMono (Z n))
    (hzero:∀n,∀i:Fin n,F n (Z n i:ℂ)=0)
    (happrox:∀k,∀e:ℝ,0 < e→∀ᶠn:ℕ in atTop,∃i:Fin n,|Z n i-sigma a ha k| < e)
    (hexcl:∀A B:ℝ,(∀x∈Icc A B,normalized (a:ℂ) (x:ℂ)≠0)→
      ∀ᶠn:ℕ in atTop,∀x∈Icc A B,F n (x:ℂ)≠0)
    (hinj:∀k,∃r:ℝ,0 < r ∧ ∀ᶠn:ℕ in atTop,InjOn (F n) (Metric.closedBall (sigma a ha k:ℂ) r))
    (k:ℕ) : Tendsto (fun n:ℕ=>finiteZeroAt Z n k) atTop (𝓝 (sigma a ha k)) := by
  -- All four zero-stability inputs are applied to the same original finite family F and list Z.
  induction k with
  | zero =>
    apply tendsto_order.mpr
    constructor
    · intro A hA
      have hN:=hexcl 0 A (fun x hx=>by
        intro hz
        exact (not_lt_of_ge ((sigma_first ha).2 hz)) (hx.2.trans_lt hA))
      filter_upwards [hN,eventually_gt_atTop (0:ℕ)] with n hn hnpos
      rw [finiteZeroAt_eq Z hnpos]
      by_contra hnot
      exact hn _ ⟨((hZ n).1 ⟨0,hnpos⟩).le,not_lt.mp hnot⟩ (hzero n ⟨0,hnpos⟩)
    · intro B hB
      filter_upwards [happrox 0 (B-sigma a ha 0) (sub_pos.mpr hB),
        eventually_gt_atTop (0:ℕ)] with n hn hnpos
      obtain ⟨i,hi⟩:=hn
      rw [finiteZeroAt_eq Z hnpos]
      exact ((hZ n).2.monotone (show (⟨0,hnpos⟩:Fin n) ≤ i from Nat.zero_le _)).trans_lt
        (by linarith [(abs_lt.mp hi).2])
  | succ k ih =>
    let P:=sigma a ha k
    let Q:=sigma a ha (k+1)
    have hPQ:P < Q:=sigma_strictMono ha (Nat.lt_succ_self k)
    apply tendsto_order.mpr
    constructor
    · intro A hA
      let L:=max A ((P+Q)/2)
      have hAL:A≤L:=le_max_left _ _
      have hPL:P < L:=lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hLQ:L < Q:=max_lt hA (by linarith)
      obtain ⟨r,hr,hI⟩:=hinj k
      let d:=min (r/2) ((L-P)/2)
      have hd:0 < d:=lt_min (half_pos hr) (half_pos (sub_pos.mpr hPL))
      have hdr:d≤r/2:=min_le_left _ _
      have hdL:d≤(L-P)/2:=min_le_right _ _
      have hgap:=hexcl (P+d) L (fun x hx=>by
        intro hz
        have hh: x∈spectralZeros a ∧ P < x:=⟨hz,by linarith [hx.1]⟩
        have hnext:Q≤x:=(sigma_successor ha k).2 hh
        linarith [hx.2])
      have hnear:=Metric.tendsto_nhds.mp ih d hd
      filter_upwards [hI,hgap,hnear,eventually_gt_atTop (k+1)] with n hnI hnGap hnNear hkn
      have hk:k < n:=by omega
      rw [finiteZeroAt_eq Z hk,Real.dist_eq] at hnNear
      rw [finiteZeroAt_eq Z hkn]
      have horder:Z n ⟨k,hk⟩ < Z n ⟨k+1,hkn⟩:=(hZ n).2 (by simp)
      have hclaim:L < Z n ⟨k+1,hkn⟩ := by
        -- An early next root is either in the zero-free gap or in the previous root's injectivity disk.
        by_contra hnot
        have hle:Z n ⟨k+1,hkn⟩≤L:=not_lt.mp hnot
        by_cases hbig:P+d≤Z n ⟨k+1,hkn⟩
        · exact hnGap _ ⟨hbig,hle⟩ (hzero n ⟨k+1,hkn⟩)
        · have hsmall:Z n ⟨k+1,hkn⟩ < P+d:=lt_of_not_ge hbig
          have hp:(Z n ⟨k,hk⟩:ℂ)∈Metric.closedBall (P:ℂ) r := by
            rw [Metric.mem_closedBall,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
            linarith
          have hq:(Z n ⟨k+1,hkn⟩:ℂ)∈Metric.closedBall (P:ℂ) r := by
            rw [Metric.mem_closedBall,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
            apply abs_le.mpr
            constructor <;> linarith [(abs_lt.mp hnNear).1]
          exact (ne_of_lt horder) (Complex.ofReal_injective
            (hnI hp hq ((hzero n ⟨k,hk⟩).trans (hzero n ⟨k+1,hkn⟩).symm)))
      exact lt_of_le_of_lt hAL hclaim
    · intro B hB
      let C:=(P+Q)/2
      have hPC:P < C:=by dsimp [C]; linarith
      have hCQ:C < Q:=by dsimp [C]; linarith
      let e:=min (B-Q) (Q-C)
      have he:0 < e:=lt_min (sub_pos.mpr hB) (sub_pos.mpr hCQ)
      have hprev:=ih.eventually (Iio_mem_nhds hPC)
      filter_upwards [happrox (k+1) e he,hprev,eventually_gt_atTop (k+1)] with n hn hprevious hkn
      have hk:k < n:=by omega
      rw [finiteZeroAt_eq Z hk] at hprevious
      rw [finiteZeroAt_eq Z hkn]
      obtain ⟨i,hi⟩:=hn
      have hiB:Z n i < B:=by
        have hh:e≤B-Q:=min_le_left _ _
        linarith [(abs_lt.mp hi).2]
      have hiC:C < Z n i:=by
        have hh:e≤Q-C:=min_le_right _ _
        linarith [(abs_lt.mp hi).1]
      have hki:(⟨k,hk⟩:Fin n) < i:=(hZ n).2.lt_iff_lt.mp (hprevious.trans hiC)
      have hk1i : (⟨k+1,hkn⟩:Fin n) ≤ i := by change k+1 ≤ i.val; exact hki
      exact ((hZ n).2.monotone hk1i).trans_lt hiB

end
end jacobi.Bessel
