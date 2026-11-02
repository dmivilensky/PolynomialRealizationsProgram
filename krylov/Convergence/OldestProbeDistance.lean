import krylov.LinearAlgebra.ProjectionGain
import krylov.Convergence.WindowMetricGain
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Article: main_krylov, thm:Ip, RFC's original stored-only distance.
Use: compare the genuine old-only and current-probe-augmented spans using
actual orthogonal projections. Source: the exact Pythagoras identity and
the synthesis-gain bound for the true projected probe.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.LinearAlgebra Submodule
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : ℕ}
set_option maxHeartbeats 800000

/-- True orthogonal distance equals the original metric infimum distance. -/
theorem infDist_eq_norm_sub_starProjection (V : Submodule ℝ E) (x : E) :
    Metric.infDist x (V:Set E)=‖x-V.starProjection x‖ := by
  rw [Metric.infDist_eq_iInf,Submodule.starProjection_minimal]
  simp only [dist_eq_norm]
  congr! 1

/- Removing the oldest column preserves the original synthesis gain. -/
omit [FiniteDimensional ℝ E] in
theorem newer_window_gain (s : Fin (p+1) → E) {σ : ℝ}
    (hg : ∀ c : Fin (p+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2)
    (c : Fin p → ℝ) :
    σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (fun i=>s i.succ) c‖^2 := by
  have hh := hg (Fin.cons 0 c)
  have he : combine s (Fin.cons 0 c)=combine (fun i=>s i.succ) c := by
    simp only [combine,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,zero_smul,zero_add]
  rw [he] at hh
  have hn : ‖WithLp.toLp 2 ((Fin.cons (0:ℝ) c):Fin (p+1) → ℝ)‖=‖WithLp.toLp 2 c‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,zero_pow (by decide : 2≠0),zero_add]
  simpa only [hn] using hh

/- The actual span of a chronological augmentation is exactly the old
span plus its genuine final direction. -/
omit [FiniteDimensional ℝ E] in
theorem span_range_snoc_window (s : Fin p → E) (d : E) :
    Submodule.span ℝ (Set.range (Fin.snoc s d))=Submodule.span ℝ (Set.range s)⊔ℝ ∙ d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [Fin.snoc_last]
      exact (show ℝ ∙ d≤_ from le_sup_right) (Submodule.mem_span_singleton_self d)
    · rw [Fin.snoc_castSucc]
      exact (show Submodule.span ℝ (Set.range s)≤_ from le_sup_left) (Submodule.subset_span ⟨j,rfl⟩)
  · apply sup_le
    · exact Submodule.span_mono (fun _ ⟨i,hi⟩=>⟨i.castSucc,by simpa only [Fin.snoc_castSucc] using hi⟩)
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      exact Submodule.subset_span ⟨Fin.last p,Fin.snoc_last _ _⟩

/-- The actual newer span of the full augmented matrix has precisely the
stored-newer columns and the real current direction. -/
theorem newerColumnSpan_snoc_window (s : Fin (p+1) → EuclideanSpace ℝ (Fin (p+2)))
    (d : EuclideanSpace ℝ (Fin (p+2))) :
    newerColumnSpan (windowMatrix (Fin.snoc s d))=
      Submodule.span ℝ (Set.range (fun i : Fin p=>s i.succ))⊔ℝ ∙ d := by
  have he : (fun i : Fin (p+1)=>euclideanColumn (windowMatrix (Fin.snoc s d)) i.succ)=
      Fin.snoc (fun j : Fin p=>s j.succ) d := by
    funext i
    change (Fin.snoc s d : Fin (p+2) → EuclideanSpace ℝ (Fin (p+2))) i.succ=_
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [show (Fin.last p).succ=Fin.last (p+1) by rfl,Fin.snoc_last,Fin.snoc_last]
    · rw [Fin.succ_castSucc,Fin.snoc_castSucc,Fin.snoc_castSucc]
  rw [newerColumnSpan,he,span_range_snoc_window]

/-- Independent old windows and vanishing actual probe pairings force the
projection of the current unit probe onto the true newer span to vanish. -/
theorem newer_probe_projection_tendsto
    (s : ℕ → Fin (p+1) → E) (d : ℕ → E) (ε : ℕ → ℝ)
    {σ : ℝ} (hσ : 0<σ) (hε : ∀ k,0≤ε k) (hεt : Tendsto ε atTop (𝓝 0))
    (hg : ∀ᶠ k in atTop,∀ c : Fin (p+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (s k) c‖^2)
    (hp : ∀ᶠ k in atTop,∀ i,|inner ℝ (s k i) (d k)|≤ε k) :
    Tendsto (fun k=>(Submodule.span ℝ (Set.range (fun i : Fin p=>s k i.succ))).starProjection (d k))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun k=>Real.sqrt p*ε k/σ)
  · filter_upwards [hg,hp] with k hkg hkp
    exact starProjection_of_gain (fun i : Fin p=>s k i.succ) (d k) hσ (hε k)
      (newer_window_gain (s k) hkg) (fun i=>hkp i.succ)
  · simpa only [mul_zero,zero_div] using (hεt.const_mul (Real.sqrt p)).div_const σ

/-- Actual near-orthogonality makes the precise projected oldest/probe
cross term vanish. The resulting squared-distance identity uses the
original stored-only span, with no unproved geometric approximation. -/
theorem oldest_probe_distance_asymptotic
    (s : ℕ → Fin (p+1) → E) (d : ℕ → E) (ε : ℕ → ℝ)
    {σ : ℝ} (hσ : 0<σ) (hε : ∀ k,0≤ε k) (hεt : Tendsto ε atTop (𝓝 0))
    (hg : ∀ᶠ k in atTop,∀ c : Fin (p+1) → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (s k) c‖^2)
    (hp : ∀ᶠ k in atTop,∀ i,|inner ℝ (s k i) (d k)|≤ε k)
    (hs : ∀ᶠ k in atTop,‖s k 0‖=1) (hd : ∀ᶠ k in atTop,‖d k‖=1) :
    let V := fun k=>Submodule.span ℝ (Set.range (fun i : Fin p=>s k i.succ))
    let theta := fun k=>inner ℝ (s k 0-(V k).starProjection (s k 0))
      ((‖d k-(V k).starProjection (d k)‖⁻¹:ℝ) • (d k-(V k).starProjection (d k)))
    Tendsto theta atTop (𝓝 0) ∧∀ᶠ k in atTop,
      Metric.infDist (s k 0) ((V k⊔ℝ ∙ d k : Submodule ℝ E):Set E)^2=
        Metric.infDist (s k 0) (V k:Set E)^2-(theta k)^2 := by
  dsimp only
  let V := fun k=>Submodule.span ℝ (Set.range (fun i : Fin p=>s k i.succ))
  let z := fun k=>(V k).starProjection (d k)
  let t := fun k=>d k-z k
  let theta := fun k=>inner ℝ (s k 0-(V k).starProjection (s k 0)) ((‖t k‖⁻¹:ℝ) • t k)
  have hz : Tendsto z atTop (𝓝 0) := newer_probe_projection_tendsto s d ε hσ hε hεt hg hp
  have hnorm : Tendsto (fun k=>‖t k‖) atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero_norm' (a:=fun k=>‖z k‖)
    · filter_upwards [hd] with k hk
      have hh := abs_norm_sub_norm_le (d k-z k) (d k)
      simpa only [t,hk,Real.norm_eq_abs,abs_abs,sub_sub_cancel_left,norm_neg] using hh
    · simpa only [norm_zero] using hz.norm
  have hinv : Tendsto (fun k=>‖t k‖⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hnorm.inv₀ one_ne_zero
  have htheta : Tendsto theta atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun k=>‖t k‖⁻¹*(ε k+‖z k‖))
    · filter_upwards [hp,hs] with k hk hsk
      have hzero : inner ℝ (s k 0-(V k).starProjection (s k 0)) (z k)=0 :=
        (V k).starProjection_inner_eq_zero _ _ ((V k).starProjection_apply_mem _)
      have he : inner ℝ (s k 0-(V k).starProjection (s k 0)) (t k)=
          inner ℝ (s k 0) (d k)-inner ℝ (s k 0) (z k) := by
        dsimp only [t]
        rw [inner_sub_right,hzero,sub_zero,inner_sub_left,
          (V k).inner_starProjection_left_eq_right]
      have hb : |inner ℝ (s k 0-(V k).starProjection (s k 0)) (t k)|≤ε k+‖z k‖ := by
        rw [he]
        exact (abs_sub _ _).trans (add_le_add (hk 0) (by
          simpa only [hsk,one_mul,Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) (s k 0) (z k)))
      simpa only [theta,Real.norm_eq_abs,real_inner_smul_right,abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
    · simpa only [norm_zero,add_zero,mul_zero] using hinv.mul (hεt.add hz.norm)
  refine ⟨htheta,?_⟩
  filter_upwards [hnorm.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))] with k hk
  have ht : t k≠0 := norm_pos_iff.mp (lt_trans (by norm_num : (0:ℝ)<1/2) hk)
  have hh := starProjection_augmented_distance (V k) (d k) (s k 0) ht
  simpa only [infDist_eq_norm_sub_starProjection,theta,t,z] using hh

/- The original synthesis gain is a lower bound for the actual oldest
column's distance to the span of all its newer stored columns. -/
omit [FiniteDimensional ℝ E] in
theorem oldest_distance_ge_gain (s : Fin (p+1) → E) {σ : ℝ} (hσ : 0≤σ)
    (hg : ∀ c : Fin (p+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2) :
    σ≤Metric.infDist (s 0) (Submodule.span ℝ (Set.range (fun i : Fin p=>s i.succ)):Set E) := by
  apply (Metric.le_infDist ⟨0,Submodule.zero_mem _⟩).mpr
  intro y hy
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  have hc' : combine (fun i : Fin p=>s i.succ) c=y := hc
  have hh := hg ((Fin.cons (1:ℝ) (fun i : Fin p=> -c i) : Fin (p+1) → ℝ))
  have he : combine s ((Fin.cons (1:ℝ) (fun i : Fin p=> -c i) : Fin (p+1) → ℝ))=s 0-y := by
    simp only [combine,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_smul,neg_smul,Finset.sum_neg_distrib]
    rw [←combine,hc']
    exact (sub_eq_add_neg _ _).symm
  have hn : 1≤‖WithLp.toLp 2 ((Fin.cons (1:ℝ) (fun i=> -c i)):Fin (p+1) → ℝ)‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,one_pow,Fin.cons_succ,neg_sq]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>sq_nonneg _)
  rw [he] at hh
  rw [dist_eq_norm]
  apply (sq_le_sq₀ hσ (norm_nonneg _)).mp
  have hz := (mul_le_mul_of_nonneg_left hn (sq_nonneg σ)).trans hh
  simpa only [mul_one] using hz

/-- A vanishing exact squared-distance loss changes inverse squared
amplification only by a real factor tending to one. -/
theorem distance_inverse_sq_comparison (a b theta : ℕ → ℝ)
    {σ : ℝ} (hσ : 0<σ) (ha : ∀ᶠ k in atTop,σ≤a k)
    (ht : Tendsto theta atTop (𝓝 0))
    (he : ∀ᶠ k in atTop,(b k)^2=(a k)^2-(theta k)^2) :
    ∃ F : ℕ → ℝ,Tendsto F atTop (𝓝 1) ∧∀ᶠ k in atTop,
      0<F k ∧((b k)^2)⁻¹≤F k*((a k)^2)⁻¹ := by
  let f := fun k=>1-(theta k)^2/σ^2
  let F := fun k=>(f k)⁻¹
  have hft : Tendsto f atTop (𝓝 1) := by
    simpa only [zero_pow (by decide : 2≠0),zero_div,sub_zero] using
      tendsto_const_nhds.sub ((ht.pow 2).div_const (σ^2))
  have hFt : Tendsto F atTop (𝓝 1) := by simpa only [inv_one] using hft.inv₀ one_ne_zero
  refine ⟨F,hFt,?_⟩
  filter_upwards [ha,he,hft.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))] with k hak hek hfk
  have hs : 0<σ^2 := sq_pos_of_pos hσ
  have has : 0<(a k)^2 := sq_pos_of_pos (hσ.trans_le hak)
  have hsq : σ^2≤(a k)^2 := pow_le_pow_left₀ hσ.le hak 2
  have hloss : (theta k)^2≤((theta k)^2/σ^2)*(a k)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (div_nonneg (sq_nonneg (theta k)) hs.le)
    simpa only [div_mul_cancel₀ _ hs.ne'] using hh
  have hprod : f k*(a k)^2≤(b k)^2 := by
    dsimp only [f]
    nlinarith only [hek,hloss]
  refine ⟨inv_pos.mpr hfk,?_⟩
  simpa only [F,mul_inv] using inv_anti₀ (mul_pos hfk has) hprod

end
end krylov.Convergence
