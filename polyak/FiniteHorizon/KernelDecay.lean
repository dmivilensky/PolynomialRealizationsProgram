import polyak.FiniteHorizon.SeparatedKernel

/-!
Article: Appendix C, Lemma kernel in a quantitative form.
Use: strict contraction on the actual zero-price class gives one uniform
exponential majorant at an exponent strictly smaller than T. This is stronger
than the single normalized-window contraction used by the main prefactor proof.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Filter
open scoped Topology

theorem exists_kernel_decay_of_nearBound {A B β T η : ℝ} {H p : ℕ}
    (L : WindowPrice H) (hp : 0<p) (hη : 0<η)
    (hnear : NearKernelBound A B β T H p η L) :
    ∃ S : ℝ,S<T ∧ ∃ C : ℝ,0<C ∧
      ∀ D : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin D)) A B β H,ZeroPriceRun L r →
        ∀ k : ℕ,windowTrace r.x H (H+k)≤C*Real.exp (2*(k : ℝ)*S)*windowTrace r.x H H := by
  have hpR : (0 : ℝ)<p:=Nat.cast_pos.mpr hp
  let S:=T-Real.log 2/(4*(p : ℝ))
  have hST : S<T:=by
    dsimp [S]
    have hh:=div_pos (Real.log_pos (by norm_num : (1 : ℝ)<2)) (by positivity : (0 : ℝ)<4*(p : ℝ))
    linarith
  have he : Real.exp (2*(p : ℝ)*T)^2/4=Real.exp (2*(2*p : ℕ)*S)/2 := by
    have hs : 2*((2*p : ℕ) : ℝ)*S=4*(p : ℝ)*T-Real.log 2:=by
      dsimp [S]
      push_cast
      field_simp [ne_of_gt hpR]
      ring
    rw [hs,Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    rw [show 4*(p : ℝ)*T=2*(p : ℝ)*T+2*(p : ℝ)*T by ring,Real.exp_add]
    ring
  obtain ⟨C,hC,hshort⟩:=exists_short_window_bound A B β S H (2*p)
  refine ⟨S,hST,C,zero_lt_one.trans_le hC,fun D r hr k => ?_⟩
  let w:=fun i => windowTrace r.x H (H+i)
  have hstep (i : ℕ) : w (i+p)≤Real.exp (2*(p : ℝ)*T)*w i/2 := by
    have hz : L (segmentWindow (r.segment (H+i+p)) (H+i))=0:=hr (H+i) (by omega)
    have hh:=hnear D (H+i+p) (r.segment (H+i+p)) (H+i) (by omega) le_rfl (by
      rw [hz]
      exact mul_nonneg hη.le (windowTrace_nonneg r.x H (H+i)))
    simpa only [w,HRun.segment,Nat.add_assoc] using hh
  have hdouble (i : ℕ) : w (i+2*p)≤Real.exp (2*(2*p : ℕ)*S)*w i/2 := by
    have h1:=hstep i
    have h2:=hstep (i+p)
    have hm:=mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2*(p : ℝ)*T)).le
    have hh : w (i+2*p)≤(Real.exp (2*(p : ℝ)*T)^2/4)*w i:=by
      rw [show i+p+p=i+2*p by omega] at h2
      nlinarith
    rw [he] at hh
    nlinarith
  have hexp (n : ℕ) : (Real.exp S)^(2*n)=Real.exp (2*(n : ℝ)*S):=by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hs : ∀ i s : ℕ,s≤2*p → w (i+s)≤C*(Real.exp S)^(2*s)*w i := by
    intro i s hsp
    simpa only [w,Nat.add_assoc,hexp] using hshort D r (H+i) s (by omega) hsp
  have hb : ∀ i,(0 : ℝ)≤1*w i → w (i+2*p)≤(Real.exp S)^(2*(2*p))*w i/2 := by
    intro i _
    simpa only [hexp] using hdouble i
  have hh:=weighted_window_bound (w:=w) (v:=fun _ => 0) (M:=0) (η:=1)
    (fun i => windowTrace_nonneg r.x H (H+i)) (Real.exp_pos S) (by norm_num) hC
    (by norm_num) (by omega : 0<2*p) (by simp) (by intro i; simp) hs hb k
  have hmax : max C (C*0/1)=C:=by simp only [mul_zero,zero_div]; exact max_eq_left (by linarith)
  simpa only [hmax,hexp,w,Nat.add_zero] using hh

/-- The actual separated kernel, including its value cancellation, gives a
strictly smaller exponent on the zero-price trajectory class. -/
theorem exists_kernel_decay_of_stationary_price {A B β T : ℝ} {H : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hRate : growthRate A B β H≤Real.exp T)
    (hpos : PriceNonnegative A B β H L) (hstep : PriceContracts A B β H T L)
    (hstationary : ∀ (ν : Spectral.Spectrum) (C : ℝ),
      Duality.FiniteFeasible (Waves.multiplierMap A B β T) T H ν C →
        0<L (stationaryWindow ν (Waves.multiplierMap A B β T) C T H)) :
    ∃ S : ℝ,S<T ∧ ∃ C : ℝ,0<C ∧
      ∀ D : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin D)) A B β H,ZeroPriceRun L r →
        ∀ k : ℕ,windowTrace r.x H (H+k)≤C*Real.exp (2*(k : ℝ)*S)*windowTrace r.x H H := by
  obtain ⟨w,ζ,ε,hw,hε,hcharge,hsymbol⟩:=stationary_kernel_separation L
    (Waves.multiplierMap A B β T) T hstationary
  let comb:=separationCombination T H w hw
  have hmem : ∀ n∈comb.lags,n≤H:=fun n hn => (Finset.mem_Icc.mp hn).2
  have hch : comb.charge+ζ*stationaryPriceCharge L T=0:=hcharge
  have hs : ∀ c,Duality.symbol (Waves.multiplierMap A B β T) T comb.lags comb.α comb.β
      comb.γplus comb.γminus c+ζ*stationaryPriceIntegrand L (Waves.multiplierMap A B β T) T c≤ -ε:=hsymbol
  obtain ⟨M,w,hM,henergy⟩:=kernelWindowEnergyBound_of_banded L
    (separatedKernel L A B β T comb ζ) (Finset.Icc 0 H) (separatedValueCoefficient L T comb ζ)
    hε (separated_kernel_symbol_le hB L comb hch hs) (separated_value_charge L T comb hmem ζ hch)
    1 (fun d r hr k hk => separated_kernel_source_nonneg hB L comb hmem r hr k hk)
  obtain ⟨p,hp,hkernel⟩:=exists_kernel_trace_contraction hB L hRate hpos hstep hM henergy
  obtain ⟨η,hη,hnear⟩:=exists_nearKernelBound_of_normalized hB L hpos hkernel
  exact exists_kernel_decay_of_nearBound L hp hη hnear

/-- The smaller exponent is uniform over all finite zero-price blocks, with
their full admissible continuation proved rather than assumed. -/
theorem exists_kernel_segment_decay_of_stationary_price {A B β T : ℝ} {H : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hRate : growthRate A B β H≤Real.exp T)
    (hpos : PriceNonnegative A B β H L) (hstep : PriceContracts A B β H T L)
    (hstationary : ∀ (ν : Spectral.Spectrum) (C : ℝ),
      Duality.FiniteFeasible (Waves.multiplierMap A B β T) T H ν C →
        0<L (stationaryWindow ν (Waves.multiplierMap A B β T) C T H)) :
    ∃ S : ℝ,S<T ∧ ∃ C : ℝ,0<C ∧ ∀ D n : ℕ,
      ∀ s : HSegment (EuclideanSpace ℝ (Fin D)) A B β H n,H≤n → L (segmentWindow s H)=0 →
        windowTrace s.x H n≤C*Real.exp (2*((n-H : ℕ) : ℝ)*S)*windowTrace s.x H H := by
  obtain ⟨S,hS,C,hC,hbound⟩:=exists_kernel_decay_of_stationary_price hB L hRate hpos hstep hstationary
  refine ⟨S,hS,C,hC,fun D n s hn hzero => ?_⟩
  obtain ⟨r,hr,_,hw⟩:=exists_zeroPriceRun hB L hpos hstep s hn hzero
  have hh:=hbound D r hr (n-H)
  rw [Nat.add_sub_of_le hn,←trace_runWindow r n hn,hw n hn le_rfl,trace_segmentWindow s n hn,
    ←trace_runWindow r H le_rfl,hw H le_rfl hn,trace_segmentWindow s H le_rfl] at hh
  exact hh

end polyak.FiniteHorizon
