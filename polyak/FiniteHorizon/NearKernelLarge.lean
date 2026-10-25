import polyak.FiniteHorizon.GlobalPrices

/-!
Article: Appendix C, the literal p*≥H bound in Lemma nearkernel.
Use: the proved strictly smaller kernel exponent permits every sufficiently
large contraction horizon. Compactness then gives the actual positive price
neighborhood for a horizon at least H.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Waves Duality Boundary Filter
open scoped Topology

theorem exists_nearKernelBound_large_of_kernel_decay {A B β T S C : ℝ} {H : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hpos : PriceNonnegative A B β H L)
    (hST : S<T) (_hC : 0<C)
    (hdecay : ∀ D n : ℕ,∀ s : HSegment (EuclideanSpace ℝ (Fin D)) A B β H n,
      H≤n → L (segmentWindow s H)=0 →
        windowTrace s.x H n≤C*Real.exp (2*((n-H : ℕ) : ℝ)*S)*windowTrace s.x H H) :
    ∃ p : ℕ,H≤p ∧ 0<p ∧ ∃ η : ℝ,0<η ∧ NearKernelBound A B β T H p η L := by
  let θ:=Real.exp (2*(S-T))
  have hθ : 0≤θ:=(Real.exp_pos _).le
  have hθ1 : θ<1:=Real.exp_lt_one_iff.mpr (by linarith)
  have hl : Tendsto (fun p : ℕ => C*θ^p) atTop (𝓝 0):=by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).const_mul C
  obtain ⟨p,hsmall,hpH,hp0⟩:=((hl.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))).and
    ((eventually_ge_atTop H).and (eventually_gt_atTop 0))).exists
  have hkernel : ∀ Y∈normalizedEndpointPairs A B β H p,L Y.1=0 →
      traceWindow Y.2<Real.exp (2*(p : ℝ)*T)/2:=by
    intro Y hY hzero
    obtain ⟨s,h0,h1,htr⟩:=normalizedEndpointPairs_sound hB hY
    have hres:=hdecay (H+p+2) (H+p) s (by omega) (by rw [←h0]; exact hzero)
    rw [show H+p-H=p by omega,←trace_segmentWindow s (H+p) (by omega),←h1,
      ←trace_segmentWindow s H le_rfl,←h0,htr,mul_one] at hres
    have hexp : θ^p*Real.exp (2*(p : ℝ)*T)=Real.exp (2*(p : ℝ)*S):=by
      dsimp [θ]
      rw [←Real.exp_nat_mul,←Real.exp_add]
      congr 1
      ring
    have hm:=mul_lt_mul_of_pos_right hsmall (Real.exp_pos (2*(p : ℝ)*T))
    rw [mul_assoc,hexp] at hm
    nlinarith
  obtain ⟨η,hη,hnear⟩:=exists_nearKernelBound_of_normalized hB L hpos hkernel
  exact ⟨p,hpH,hp0,η,hη,hnear⟩

/-- Every q has the source's literal near-kernel estimate, for every retained
memory above one threshold, with p*≥H and all source inputs discharged. -/
theorem exists_global_exact_price_and_nearkernel {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃ H₀ : ℕ,7≤H₀ ∧ ∀ H : ℕ,H₀≤H →
      ∃ L : WindowPrice H,PriceNonnegative 0 (2*q) (q^2) H L ∧
        PriceContracts 0 (2*q) (q^2) H (T q) L ∧
        (∀ (ν : Spectrum) (C : ℝ),FiniteFeasible (multiplierMap 0 (2*q) (q^2) (T q)) (T q) H ν C →
          Real.exp (2*(H-5 : ℕ)*T q)/2≤
            L (stationaryWindow ν (multiplierMap 0 (2*q) (q^2) (T q)) C (T q) H)) ∧
        ∃ p : ℕ,H≤p ∧ 0<p ∧ ∃ η : ℝ,0<η ∧ NearKernelBound 0 (2*q) (q^2) (T q) H p η L := by
  obtain ⟨H₀,hH₀,hprices⟩:=exists_global_exact_price_and_kernel_decay hq hq1
  refine ⟨H₀,hH₀,fun H hH => ?_⟩
  obtain ⟨_,L,hpos,hstep,hreserve,S,hST,C,hC,hdecay⟩:=hprices H hH
  exact ⟨L,hpos,hstep,hreserve,
    exists_nearKernelBound_large_of_kernel_decay (by positivity) L hpos hST hC hdecay⟩

end polyak.FiniteHorizon
