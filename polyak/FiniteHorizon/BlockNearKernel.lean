import polyak.FiniteHorizon.BlockEndpoints
import polyak.Growth.HorizonBound

/-!
Article: Appendix C, actual compact-neighborhood contraction.
Use: global Gram-cone homogeneity extends the normalized compactness argument
to every finite admissible segment, in every real Hilbert dimension.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Matrix
open scoped Topology Matrix.Norms.Elementwise

theorem blockCone_smul {A B β r : ℝ} {H n : ℕ} {Y : WindowSpace n}
    (hr : 0≤r) (hY : Y∈blockCone A B β H n) : r • Y∈blockCone A B β H n := by
  refine ⟨hY.1.smul hr,?_,?_⟩
  · intro i
    rw [map_smul,map_smul,smul_eq_mul,smul_eq_mul,abs_mul,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (hY.2.1 i) hr
  · intro i j hij
    rw [map_smul,map_smul,smul_eq_mul,smul_eq_mul,abs_mul,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (hY.2.2 i j hij) hr

theorem sliceWindow_smul {H p : ℕ} (l : ℕ) (hl : l≤p) (r : ℝ) (Y : WindowSpace (H+p)) :
    sliceWindow l hl (r • Y)=r • sliceWindow l hl Y := by
  apply Prod.ext
  · ext i j
    rfl
  · ext i
    rfl

theorem blockPrefixTrace_smul (H n : ℕ) (hHN : H≤n) (r : ℝ) (Y : WindowSpace n) :
    blockPrefixTrace H n hHN (r • Y)=r*blockPrefixTrace H n hHN Y := by
  unfold blockPrefixTrace
  rw [Finset.mul_sum]
  rfl

theorem segmentWindow_restrict_center {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n)
    (l m : ℕ) (hl : l+m≤n) (k : ℕ) (hk : H≤k) :
    segmentWindow (s.restrict l m hl) k=segmentWindow s (l+k) := by
  apply Prod.ext
  · ext i j
    change inner ℝ (s.x (l+(k-H+i))) (s.x (l+(k-H+j)))=
      inner ℝ (s.x (l+k-H+i)) (s.x (l+k-H+j))
    have hi : l+(k-H+i.val)=l+k-H+i.val:=by omega
    have hj : l+(k-H+j.val)=l+k-H+j.val:=by omega
    rw [hi,hj]
  · ext i
    change s.value (l+(k-H+(i+1)))=s.value (l+k-H+(i+1))
    congr 1
    omega

theorem scaled_endpoints_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H p : ℕ} (hB : B≠0) (s : HSegment E A B β H (H+p))
    {τ : ℝ} (hτ : 0<τ) (ht : traceWindow (segmentWindow s H)=τ) :
    ((1/τ) • segmentWindow s H,(1/τ) • segmentWindow s (H+p))∈
      normalizedEndpointPairs A B β H p := by
  have hprefix : blockPrefixTrace H (H+p) (by omega) (blockOfSegment s)=τ :=by
    rw [←trace_sliceWindow_zero,sliceWindow_blockOfSegment]
    simpa only [Nat.add_zero] using ht
  refine ⟨(1/τ) • blockOfSegment s,⟨blockCone_smul (by positivity) (blockOfSegment_mem hB s),?_⟩,?_⟩
  · rw [blockPrefixTrace_smul,hprefix,one_div_mul_cancel hτ.ne']
  · apply Prod.ext
    · change sliceWindow 0 (Nat.zero_le p) ((1/τ) • blockOfSegment s)=(1/τ) • segmentWindow s H
      rw [sliceWindow_smul,sliceWindow_blockOfSegment]
      simp only [Nat.add_zero]
    · change sliceWindow p le_rfl ((1/τ) • blockOfSegment s)=(1/τ) • segmentWindow s (H+p)
      rw [sliceWindow_smul,sliceWindow_blockOfSegment]

/-- Strict normalized kernel contraction gives the full finite-segment near-kernel
bound used in the final envelope-prefactor theorem. -/
theorem exists_nearKernelBound_of_normalized {A B β T : ℝ} {H p : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hpos : PriceNonnegative A B β H L)
    (hkernel : ∀ Y∈normalizedEndpointPairs A B β H p,L Y.1=0 →
      traceWindow Y.2<Real.exp (2*(p : ℝ)*T)/2) :
    ∃ η : ℝ,0<η ∧ NearKernelBound A B β T H p η L := by
  obtain ⟨η,hη,hηgood⟩:=exists_near_kernel_contraction L _
    (normalizedEndpointPairs_isCompact A B β H p hB)
    (fun Y hY => by
      obtain ⟨s,h0,_,_⟩:=normalizedEndpointPairs_sound hB hY
      rw [h0]
      exact hpos _ (segmentWindow_mem hB s H le_rfl (by omega))) hkernel
  refine ⟨η,hη,?_⟩
  intro d n s k hk hkn hsmall
  let τ:=traceWindow (segmentWindow s k)
  have hτ : 0≤τ:=traceWindow_nonneg (segmentWindow_mem hB s k hk (by omega))
  have htrace : τ=windowTrace s.x H k:=trace_segmentWindow s k hk
  by_cases hzero : τ=0
  · have hbound:=windowTrace_add_le s k p hk hkn
    rw [←htrace,hzero,mul_zero] at hbound
    simpa only [←htrace,hzero,mul_zero,zero_div] using hbound
  · have hτpos : 0<τ:=lt_of_le_of_ne hτ (Ne.symm hzero)
    let q:=s.restrict (k-H) (H+p) (by omega)
    have h0 : segmentWindow q H=segmentWindow s k:=by
      rw [segmentWindow_restrict_center s (k-H) (H+p) (by omega) H le_rfl]
      congr 1
      omega
    have h1 : segmentWindow q (H+p)=segmentWindow s (k+p):=by
      rw [segmentWindow_restrict_center s (k-H) (H+p) (by omega) (H+p) (by omega)]
      congr 1
      omega
    have hpair:=scaled_endpoints_mem hB q hτpos (by rw [h0])
    have hsm : L ((1/τ) • segmentWindow q H)≤η:=by
      rw [map_smul,smul_eq_mul,h0]
      rw [one_div,mul_comm,←div_eq_mul_inv]
      apply (div_le_iff₀ hτpos).mpr
      simpa only [←htrace] using hsmall
    have hc:=hηgood _ hpair hsm
    change traceWindow ((1/τ) • segmentWindow q (H+p))<Real.exp (2*(p : ℝ)*T)/2 at hc
    rw [h1] at hc
    change Matrix.trace ((1/τ) • (segmentWindow s (k+p)).1)<Real.exp (2*(p : ℝ)*T)/2 at hc
    rw [Matrix.trace_smul,smul_eq_mul] at hc
    change (1/τ)*traceWindow (segmentWindow s (k+p))<Real.exp (2*(p : ℝ)*T)/2 at hc
    have hfinal : traceWindow (segmentWindow s (k+p))≤Real.exp (2*(p : ℝ)*T)*τ/2 := by
      have hc' : traceWindow (segmentWindow s (k+p))/τ<Real.exp (2*(p : ℝ)*T)/2 := by
        calc
          _=(1/τ)*traceWindow (segmentWindow s (k+p)) := by ring
          _<_ := hc
      have hh:=(div_lt_iff₀ hτpos).mp hc'
      nlinarith
    simpa only [trace_segmentWindow s (k+p) (by omega),htrace] using hfinal

end polyak.FiniteHorizon
