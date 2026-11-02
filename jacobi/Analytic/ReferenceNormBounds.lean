import jacobi.Analytic.GammaBounds

/-!
Article: jacobi, Lemma C.1.
The printed continued reference norms satisfy the full two-sided index
power bounds uniformly on every compact set of complex orders with
positive endpoint exponent. The genuine finite prefix and the infinite
Gamma-ratio tail are both included, without numerical certificates.
Use: bounds the actual reference normalization and the two finite prefix norms in Lemma C.1.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A continuous nowhere-zero function has two positive uniform norm bounds on a nonempty compact set.
Use: bounds the actual reference normalization and the two finite prefix norms in Lemma C.1.
Article: jacobi, Lemma C.1.
Source: the extreme value theorem, as formalized in mathlib.
Proof: minimize the actual positive norm on the compact set and use
the compact continuous-image upper bound, enlarged by one. -/
theorem compact_nonzero_norm_bounds {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) (hfn : ∀ a∈K,f a≠0) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ a∈K,c≤‖f a‖ ∧ ‖f a‖≤C := by
  obtain ⟨a,ha,hmin⟩ := hK.exists_isMinOn hne hf.norm
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hf
  exact ⟨‖f a‖,|B|+1,norm_pos_iff.mpr (hfn a ha),by positivity,
    fun z hz => ⟨hmin hz,(hB z hz).trans (by linarith [le_abs_self B])⟩⟩

/-- The original continued reference norm with its natural complex index normalization.
Use: turns the finite-prefix normalized norms into actual continuous nonzero functions of order.
Article: jacobi, Lemma C.1.
-/
def scaledNorming (a : ℂ) (n : ℕ) : ℂ := norming a n*((n+1:ℝ):ℂ)^(2*gamma a)

/-- The actual normalized reference norm is analytic in the complex order at every admissible exponent.
Use: compactness controls the genuine two finite initial norms in the full all-index estimate.
Article: jacobi, Lemma C.1.
Proof: the actual norm quotient is holomorphic and its positive-index
power has an analytic affine exponent and a fixed positive base. -/
theorem scaledNorming_analytic {a : ℂ} (ha : 0<(gamma a).re) (n : ℕ) :
    AnalyticAt ℂ (fun b => scaledNorming b n) a := by
  have hg : AnalyticAt ℂ gamma a := by unfold gamma; fun_prop
  have hp := (analyticAt_const (v := ((n+1:ℝ):ℂ))).cpow ((analyticAt_const (v := (2:ℂ))).mul hg)
    (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp only [Complex.ofReal_re]; positivity)))
  exact (norming_comp_analytic analyticAt_id ha n).mul hp

/-- The actual complex-normalized norm has exactly the original real-part index-power norm.
Use: translates holomorphic finite-prefix compact bounds into the precise printed power law.
Article: jacobi, Lemma C.1.
Proof: the index base is positive, so its complex-power norm is its
real-part power. Norm multiplicativity gives the original normalization. -/
theorem scaledNorming_norm (a : ℂ) (n : ℕ) :
    ‖scaledNorming a n‖=‖norming a n‖*(n+1:ℝ)^(2*(gamma a).re) := by
  rw [scaledNorming,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  norm_num

/-- The actual normalized reference norm is nonzero everywhere in its original positive-exponent half-plane.
Use: the genuine finite prefix has a strictly positive compact minimum.
Article: jacobi, Lemma C.1.
Proof: the proved norm quotient is nonzero and the positive-index
complex power has nonzero base, hence is nonzero as well. -/
theorem scaledNorming_ne_zero {a : ℂ} (ha : 0<(gamma a).re) (n : ℕ) : scaledNorming a n≠0 :=
  mul_ne_zero (norming_ne_zero ha n) (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity))))

/-- The original continued reference norms have both uniform positive power bounds on every compact admissible complex-order set, including every original index.
Use: supplies the genuine denominator estimates required by the actual analytic GL kernel and profile series.
Article: jacobi, Lemma C.1.
Proof: the compact order set gives positive lower and upper affine
exponent bounds and positive bounds on the actual normalization scalar.
Apply the proved compact complex Gamma-ratio estimate to twice that
exponent. The remaining affine index factor has uniform linear bounds.
Their exact product is the normalized norm. The original indices zero
and one are controlled by compactness of their actual nonzero normalized
norm functions, so the tail estimate extends to all indices. -/
theorem norming_bounds {K : Set ℂ} (hK : IsCompact K) (hpos : ∀ a∈K,0<(gamma a).re) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ a∈K,∀ n : ℕ,
      c/(n+1:ℝ)^(2*(gamma a).re)≤‖norming a n‖ ∧
      ‖norming a n‖≤C/(n+1:ℝ)^(2*(gamma a).re) := by
  -- The finite prefix and infinite tail concern the same original Gamma normalization.
  by_cases hne : K.Nonempty
  · have hg : Continuous gamma := by unfold gamma; fun_prop
    obtain ⟨a0,ha0,hmin⟩ := hK.exists_isMinOn hne (Complex.continuous_re.comp hg).continuousOn
    let d : ℝ := min 1 (gamma a0).re
    have hd : 0<d := lt_min (by norm_num) (hpos a0 ha0)
    have hd1 : d≤1 := min_le_left _ _
    have hdg (a : ℂ) (ha : a∈K) : d≤(gamma a).re := (min_le_right _ _).trans (hmin ha)
    obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    let G : ℝ := |B|+1
    have hG : 0<G := by dsimp [G]; positivity
    have hGg (a : ℂ) (ha : a∈K) : ‖gamma a‖≤G := (hB a ha).trans (by dsimp [G]; linarith [le_abs_self B])
    obtain ⟨cA,CA,hcA,hCA,hA⟩ := compact_nonzero_norm_bounds hK hne
      (fun a ha => (normConstant_comp_analytic analyticAt_id (hpos a ha)).continuousAt.continuousWithinAt)
      (fun a ha => normConstant_ne_zero (hpos a ha))
    have hGammaK : IsCompact ((fun a => 2*gamma a) '' K) := hK.image (by fun_prop)
    obtain ⟨cR,CR,hcR,hCR,hR⟩ := gamma_ratio_compact_tail hGammaK (by
      rintro s ⟨a,ha,rfl⟩
      norm_num
      linarith [hpos a ha])
    have hprefix (n : ℕ) : ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ a∈K,
        c≤‖scaledNorming a n‖ ∧ ‖scaledNorming a n‖≤C :=
      compact_nonzero_norm_bounds hK hne
        (fun a ha => (scaledNorming_analytic (hpos a ha) n).continuousAt.continuousWithinAt)
        (fun a ha => scaledNorming_ne_zero (hpos a ha) n)
    obtain ⟨c0,C0,hc0,hC0,h0⟩ := hprefix 0
    obtain ⟨c1,C1,hc1,hC1,h1⟩ := hprefix 1
    let ct : ℝ := cA*cR/(G+1)
    let Ct : ℝ := CA*CR/d
    have hct : 0<ct := by dsimp [ct]; positivity
    have hCt : 0<Ct := by dsimp [Ct]; positivity
    let c : ℝ := min ct (min c0 c1)
    let C : ℝ := Ct+C0+C1
    have hc : 0<c := lt_min hct (lt_min hc0 hc1)
    have hC : 0<C := by dsimp [C]; positivity
    refine ⟨c,C,hc,hC,fun a ha n => ?_⟩
    have hnp : 0<(n+1:ℝ) := by positivity
    have hpow : 0<(n+1:ℝ)^(2*(gamma a).re) := Real.rpow_pos_of_pos hnp _
    suffices hn : c≤‖scaledNorming a n‖ ∧ ‖scaledNorming a n‖≤C by
      rw [scaledNorming_norm] at hn
      exact ⟨(div_le_iff₀ hpow).mpr hn.1,(le_div_iff₀ hpow).mpr hn.2⟩
    by_cases htail : 2≤n
    · have hk : 0<((n:ℂ)+gamma a).re := by
        simp only [Complex.add_re,Complex.natCast_re]
        have hp := hpos a ha
        positivity
      have hlinp : 0<‖(n:ℂ)+gamma a‖ := (hk.trans_le (Complex.re_le_norm _))
      have hlinlo : d*(n+1:ℝ)≤‖(n:ℂ)+gamma a‖ := by
        apply le_trans _ (Complex.re_le_norm _)
        simp only [Complex.add_re,Complex.natCast_re]
        nlinarith [hdg a ha,mul_nonneg (sub_nonneg.mpr hd1) (Nat.cast_nonneg (α := ℝ) n)]
      have hlinhi : ‖(n:ℂ)+gamma a‖≤(G+1)*(n+1:ℝ) := by
        have hh := norm_add_le (n:ℂ) (gamma a)
        rw [Complex.norm_natCast] at hh
        nlinarith [hGg a ha,mul_nonneg hG.le (Nat.cast_nonneg (α := ℝ) n)]
      have hreci : 1/(G+1)≤(n+1:ℝ)/‖(n:ℂ)+gamma a‖ ∧
          (n+1:ℝ)/‖(n:ℂ)+gamma a‖≤1/d := by
        constructor
        · exact (div_le_div_iff₀ (by positivity : (0:ℝ)<G+1) hlinp).mpr (by nlinarith [hlinhi])
        · exact (div_le_div_iff₀ hlinp hd).mpr (by nlinarith [hlinlo])
      have hR' := hR (2*gamma a) ⟨a,ha,rfl⟩ n htail
      norm_num at hR'
      have he : ‖scaledNorming a n‖=‖normConstant a‖*
          (Real.Gamma ((n:ℝ)+1)/‖Complex.Gamma ((n:ℂ)+2*gamma a)‖*(n+1:ℝ)^(2*(gamma a).re-1))*
            ((n+1:ℝ)/‖(n:ℂ)+gamma a‖) := by
        rw [scaledNorming_norm,norming,norm_div,norm_mul,norm_mul]
        have hnat : ‖Complex.Gamma ((n:ℂ)+1)‖=Real.Gamma ((n:ℝ)+1) := by
          rw [Complex.Gamma_nat_eq_factorial,Complex.norm_natCast,Real.Gamma_nat_eq_factorial]
        rw [hnat]
        have hp : (n+1:ℝ)^(2*(gamma a).re)=(n+1:ℝ)^(2*(gamma a).re-1)*(n+1:ℝ) := by
          rw [← Real.rpow_add_one hnp.ne']
          congr 1
          ring
        rw [hp]
        ring
      have htbound : ct≤‖scaledNorming a n‖ ∧ ‖scaledNorming a n‖≤Ct := by
        rw [he]
        constructor
        · have hh := mul_le_mul
            (mul_le_mul (hA a ha).1 hR'.1 hcR.le (norm_nonneg _)) hreci.1 (by positivity) (by positivity)
          exact (by simpa only [ct,div_eq_mul_inv,one_mul,id_eq] using hh)
        · have hh := mul_le_mul
            (mul_le_mul (hA a ha).2 hR'.2 (by positivity) hCA.le) hreci.2
              (by positivity) (by positivity)
          exact (by simpa only [Ct,div_eq_mul_inv,one_mul,id_eq] using hh)
      exact ⟨(min_le_left _ _).trans htbound.1,htbound.2.trans (by dsimp [C]; linarith)⟩
    · have hn : n=0 ∨ n=1 := by omega
      rcases hn with rfl | rfl
      · exact ⟨((min_le_right _ _).trans (min_le_left _ _)).trans (h0 a ha).1,
          (h0 a ha).2.trans (by dsimp [C]; linarith)⟩
      · exact ⟨((min_le_right _ _).trans (min_le_right _ _)).trans (h1 a ha).1,
          (h1 a ha).2.trans (by dsimp [C]; linarith)⟩
  · exact ⟨1,1,by norm_num,by norm_num,fun a ha => False.elim (hne ⟨a,ha⟩)⟩

end
end jacobi.ComplexReference
