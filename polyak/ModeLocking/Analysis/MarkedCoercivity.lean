import polyak.ModeLocking.Analysis.Coercivity

/-! Extra marked points need not be actual zeros. This includes the origin
when the minimizer multiplier is positive. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set Metric

theorem finite_marked_zero_coercivity {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (hne:Z.Nonempty) (hz:∀z∈Z,z∈Icc a b)
    (hf:∀x∈Icc a b,ContDiffAt ℝ 2 f x)
    (hc2:ContinuousOn (iteratedDeriv 2 f) (Icc a b))
    (hneg:∀x∈Icc a b,f x≤0)
    (hslope:∀z∈Z,f z=0→deriv f z=0)
    (hcurv:∀z∈Z,f z=0→iteratedDeriv 2 f z<0)
    (hstrict:∀x∈Icc a b,x∉Z→f x<0) :
    ∃c:ℝ,0<c ∧ ∀x∈Icc a b,c*(infDist x (Z:Set ℝ))^2≤-f x := by
  classical
  let A:=Z.filter (fun z=>f z=0)
  by_cases hA:A.Nonempty
  · have hcent:∀z∈A,z∈Icc a b:=fun z h=>hz z (Finset.mem_filter.mp h).1
    have hzero:∀z∈A,f z=0:=fun _ h=>(Finset.mem_filter.mp h).2
    have hd:∀z∈A,deriv f z=0:=fun z h=>hslope z (Finset.mem_filter.mp h).1 (hzero z h)
    have hdd:∀z∈A,iteratedDeriv 2 f z<0:=fun z h=>hcurv z (Finset.mem_filter.mp h).1 (hzero z h)
    have hstrictA:∀x∈Icc a b,x∉A→f x<0:=by
      intro x hx hn
      apply lt_of_le_of_ne (hneg x hx)
      intro he
      apply hn
      exact Finset.mem_filter.mpr ⟨by by_contra h;exact (hstrict x hx h).ne he,he⟩
    obtain ⟨c,hc,hbound⟩:=finite_zero_quadratic_coercivity hA hcent hf hc2 hzero hd hdd hstrictA
    refine ⟨c,hc,fun x hx=>?_⟩
    have hsub:(A:Set ℝ)⊆(Z:Set ℝ):=by intro z h;exact (Finset.mem_filter.mp h).1
    have hdist:infDist x (Z:Set ℝ)≤ infDist x (A:Set ℝ):=infDist_le_infDist_of_subset hsub hA
    have hsq:(infDist x (Z:Set ℝ))^2≤(infDist x (A:Set ℝ))^2:=by
      nlinarith [infDist_nonneg (x:=x) (s:=(Z:Set ℝ)),infDist_nonneg (x:=x) (s:=(A:Set ℝ))]
    exact (mul_le_mul_of_nonneg_left hsq hc.le).trans (hbound x hx)
  · have hstrictAll:∀x∈Icc a b,f x<0:=by
      intro x hx
      apply lt_of_le_of_ne (hneg x hx)
      intro he
      have hzZ:x∈Z:=by by_contra h;exact (hstrict x hx h).ne he
      exact hA ⟨x,Finset.mem_filter.mpr ⟨hzZ,he⟩⟩
    obtain ⟨z,hzZ⟩:=hne
    have hcont:ContinuousOn f (Icc a b):=fun x hx=>(hf x hx).continuousAt.continuousWithinAt
    obtain ⟨y,hy,hmax⟩:=isCompact_Icc.exists_isMaxOn ⟨z,hz z hzZ⟩ hcont
    let η:= -f y
    have hη:0<η:=neg_pos.mpr (hstrictAll y hy)
    refine ⟨η/((b-a)^2+1),by positivity,fun x hx=>?_⟩
    have hdist:infDist x (Z:Set ℝ)≤|x-z|:=by
      simpa only [Real.dist_eq] using infDist_le_dist_of_mem (show z∈(Z:Set ℝ) from hzZ)
    have hzb:=hz z hzZ
    have hb:0≤b-a:=by linarith [hx.1,hx.2]
    have hB:|x-z|≤b-a:=abs_le.mpr ⟨by linarith [hzb.2,hx.1],by linarith [hx.2,hzb.1]⟩
    have hsq:(infDist x (Z:Set ℝ))^2≤(b-a)^2+1:=by
      nlinarith [infDist_nonneg (x:=x) (s:=(Z:Set ℝ))]
    have hmul:η/((b-a)^2+1)*(infDist x (Z:Set ℝ))^2≤η:=by
      calc
        _≤η/((b-a)^2+1)*((b-a)^2+1):=mul_le_mul_of_nonneg_left hsq (by positivity)
        _=η:=div_mul_cancel₀ _ (by positivity)
    have hmax':f x≤f y:=hmax hx
    dsimp [η] at hmul
    linarith

end polyak.ModeLocking.Analysis
