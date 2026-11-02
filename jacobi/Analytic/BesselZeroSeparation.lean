import jacobi.Analytic.BesselAllZeros
import jacobi.Analysis.FiniteNormNeighborhood
import jacobi.Hankel.ReferenceSeparation

/-!
Article: jacobi, Lemma E.1.
Use: the analytic norming products and inverse GL construction use these actual all-index branches, their genuine reference errors, and nonzero uniformly separated denominators.
-/
namespace jacobi.Bessel
noncomputable section
open Set Metric Filter jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The complete original numbered Bessel spectral family satisfies all three assertions of Lemma E.1 on one common complex-order disk, with no asymptotic or continuation premises.
Use: the analytic norming products and inverse GL construction use these actual all-index branches, their genuine reference errors, and nonzero uniformly separated denominators.
Article: jacobi, Lemma E.1.
Proof: start from the proved full numbered holomorphic Bessel family. Its genuine reference separation absorbs both actual perturbation errors whenever either index is large. On the remaining finite index set, the original positive distinct real spectrum gives a positive common norm bound for every branch and pairwise difference on a smaller disk. Combine this finite bound with the actual quadratic tail nonvanishing and the large-pair separation. -/
theorem uniform_numbered_bessel_zeros {a0 : ℝ} (ha0 : -1<a0) :
    ∃ r C c : ℝ,∃ S : ℕ → ℂ → ℂ,0<r ∧ r<a0+1 ∧ 0<C ∧ 0<c ∧
      (∀ k : ℕ,DifferentiableOn ℂ (S k) (ball (a0:ℂ) r)) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖<r → ∀ k : ℕ,S k (b:ℂ)=(sigma b hb k:ℂ)) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k : ℕ,normalized a (S k a)=0 ∧
        ‖S k a-frequencyReference a k‖≤C/(k+1:ℝ)^2 ∧ c*(k+1:ℝ)^2≤‖S k a‖) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k l : ℕ,k≠l →
        c*|(l+1:ℝ)^2-(k+1:ℝ)^2|≤‖S l a-S k a‖) := by
  -- Every finite center value below is an actual positive simple original Bessel zero.
  classical
  obtain ⟨r,C,N,S,hr,_hr1,hra,hC,hN,hSa,hSe,hSreal,hSlow,_hSsep⟩ := full_numbered_bessel_family ha0
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C+1)
  let L : ℕ := max N M
  have hNL : N≤L := le_max_left _ _
  have hL1 : 1≤L := hN.trans hNL
  have hLp : 0<(L:ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hL1
  have hLlarge : 2*C+1<(L:ℝ) := hM.trans_le (by exact_mod_cast (le_max_right N M))
  let I := Fin L ⊕ {p : Fin L × Fin L // p.1≠p.2}
  let F : I → ℂ → ℂ := Sum.elim (fun i => S i) (fun p a => S p.val.2 a-S p.val.1 a)
  have hSbase (k : ℕ) : S k (a0:ℂ)=(sigma a0 ha0 k:ℂ) := hSreal a0 ha0 (by simpa using hr) k
  have hScont (k : ℕ) : ContinuousAt (S k) (a0:ℂ) :=
    (hSa k).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr)) |>.continuousAt
  have hFcont (i : I) : ContinuousAt (F i) (a0:ℂ) := by
    rcases i with i | p
    · exact hScont i
    · exact (hScont p.val.2).sub (hScont p.val.1)
  have hFnonzero (i : I) : F i (a0:ℂ)≠0 := by
    rcases i with i | p
    · change S i (a0:ℂ)≠0
      rw [hSbase]
      exact Complex.ofReal_ne_zero.mpr (spectralZero_pos ha0 (sigma_mem ha0 i)).ne'
    · change S p.val.2 (a0:ℂ)-S p.val.1 (a0:ℂ)≠0
      rw [hSbase,hSbase]
      apply sub_ne_zero.mpr
      intro he
      apply p.property
      apply Fin.ext
      exact ((sigma_strictMono ha0).injective (Complex.ofReal_injective he)).symm
  let _ : Nonempty I := ⟨Sum.inl ⟨0,by omega⟩⟩
  obtain ⟨d,hd,hnear⟩ := jacobi.Analysis.finite_norm_neighborhood hFcont hFnonzero
  obtain ⟨ρ,hρ,hρdata⟩ := Metric.mem_nhds_iff.mp hnear
  let q : ℝ := min r ρ
  have hq : 0<q := lt_min hr hρ
  have hqr : q≤r := min_le_left _ _
  have hqρ : q≤ρ := min_le_right _ _
  let c : ℝ := min (1/4) (d/(L:ℝ)^2)
  have hc : 0<c := lt_min (by norm_num) (div_pos hd (sq_pos_of_pos hLp))
  have hcquarter : c≤1/4 := min_le_left _ _
  have hcL : c*(L:ℝ)^2≤d := (le_div_iff₀ (sq_pos_of_pos hLp)).mp (min_le_right _ _)
  have hfinite {a : ℂ} (ha : ‖a-(a0:ℂ)‖<q) (i : I) : d≤‖F i a‖ :=
    hρdata (by simpa only [mem_ball,dist_eq_norm] using ha.trans_le hqρ) i
  have hindex (k : ℕ) (hk : k<L) : (k+1:ℝ)^2≤(L:ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_one_le_iff.mpr hk) 2
  have hnorm {a : ℂ} (ha : ‖a-(a0:ℂ)‖<q) (k : ℕ) : c*(k+1:ℝ)^2≤‖S k a‖ := by
    by_cases hk : k<L
    · exact ((mul_le_mul_of_nonneg_left (hindex k hk) hc.le).trans hcL).trans (hfinite ha (Sum.inl ⟨k,hk⟩))
    · have hLk : L≤k := not_lt.mp hk
      have hk1 : 1≤(k:ℝ) := by exact_mod_cast hL1.trans hLk
      have hh := hSlow a (ha.trans_le hqr) k (hNL.trans hLk)
      exact ((mul_le_mul_of_nonneg_right hcquarter (by positivity : (0:ℝ)≤(k+1:ℝ)^2)).trans
        (by nlinarith : (1/4:ℝ)*(k+1:ℝ)^2≤(k:ℝ)^2)).trans hh
  refine ⟨q,C,c,S,hq,hqr.trans_lt hra,hC,hc,
    (fun k => (hSa k).mono (ball_subset_ball hqr)),
    (fun b hb ha k => hSreal b hb (ha.trans_le hqr) k),
    (fun a ha k => ⟨(hSe a (ha.trans_le hqr) k).1,(hSe a (ha.trans_le hqr) k).2,hnorm ha k⟩),?_⟩
  intro a ha k l hkl
  let Q : ℝ := |(l+1:ℝ)^2-(k+1:ℝ)^2|
  by_cases hsmall : k<L ∧ l<L
  · have hQ : Q≤(L:ℝ)^2 := by
      have hk := hindex k hsmall.1
      have hl := hindex l hsmall.2
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg (l+1:ℝ)],by nlinarith [sq_nonneg (k+1:ℝ)]⟩
    have hp : (⟨k,hsmall.1⟩:Fin L)≠⟨l,hsmall.2⟩ := by intro he; exact hkl (congrArg Fin.val he)
    have hh := hfinite ha (Sum.inr ⟨(⟨k,hsmall.1⟩,⟨l,hsmall.2⟩),hp⟩)
    exact ((mul_le_mul_of_nonneg_left hQ hc.le).trans hcL).trans hh
  · have hlarge : L≤max k l := by omega
    have hlargeR : (L:ℝ)≤max (k:ℝ) (l:ℝ) := by exact_mod_cast hlarge
    have hQlarge : 2*C≤Q := (by linarith : (2*C:ℝ)≤(L:ℝ)).trans
      (hlargeR.trans (quadratic_index_gap_lower hkl))
    have hreal : -1<a.re := by
      have hh := Complex.re_le_norm ((a0:ℂ)-a)
      rw [norm_sub_rev] at hh
      simp only [Complex.sub_re,Complex.ofReal_re] at hh
      have har : ‖a-(a0:ℂ)‖<r := ha.trans_le hqr
      linarith
    have herr (j : ℕ) : ‖S j a-frequencyReference a j‖≤C :=
      (hSe a (ha.trans_le hqr) j).2.trans (div_le_self hC.le (by nlinarith [Nat.cast_nonneg (α := ℝ) j]))
    have heq : frequencyReference a l-frequencyReference a k=(S l a-S k a)-
        (S l a-frequencyReference a l)+(S k a-frequencyReference a k) := by ring
    have htriangle : ‖frequencyReference a l-frequencyReference a k‖≤‖S l a-S k a‖+2*C := by
      rw [heq]
      exact ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl (herr l)))
        (herr k))).trans_eq (by ring)
    have hRef := frequencyReference_separated hreal hkl
    have hfinal : Q≤‖S l a-S k a‖ := by change 2*Q≤_ at hRef; linarith
    exact (mul_le_of_le_one_left (abs_nonneg _) (hcquarter.trans (by norm_num))).trans hfinal

end
end jacobi.Bessel
