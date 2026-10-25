import polyak.ModeLocking.Analysis.JetCover
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Primary finite-zero C2 hypotheses produce the quantitative jet cover.
No neighborhood, complement margin, or quadratic estimate is assumed. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set

theorem exists_negativeJetCover {a b:ℝ} {Z:Finset ℝ} {f:ℝ→ℝ}
    (hne:Z.Nonempty) (hz:∀z∈Z,z∈Icc a b)
    (hf:∀x∈Icc a b,ContDiffAt ℝ 2 f x)
    (hc2:ContinuousOn (iteratedDeriv 2 f) (Icc a b))
    (hzero:∀z∈Z,f z=0) (hslope:∀z∈Z,deriv f z=0)
    (hcurv:∀z∈Z,iteratedDeriv 2 f z<0)
    (hstrict:∀x∈Icc a b,x∉Z→f x<0) : Nonempty (NegativeJetCover a b Z f) := by
  classical
  have hZ:Set.Nonempty (Z:Set ℝ):=hne
  obtain ⟨z,hzZ,hmax⟩:=Z.finite_toSet.isCompact.exists_isMaxOn hZ
    (hc2.mono (fun z hzZ=>hz z hzZ))
  let η:= -iteratedDeriv 2 f z/2
  have hη:0<η:=by dsimp [η];linarith [hcurv z hzZ]
  obtain ⟨r,hr,huniform⟩:=Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc2) η hη
  let δ:=r/2
  have hδ:0<δ:=by dsimp [δ];positivity
  have hlocal:∀z∈Z,∀x∈Icc a b,|x-z|≤δ→iteratedDeriv 2 f x≤-η:=by
    intro w hw x hx hnear
    have hd:dist x w<r:=by rw [Real.dist_eq];dsimp [δ] at hnear;linarith
    have hh:=huniform x hx w (hz w hw) hd
    rw [Real.dist_eq,abs_lt] at hh
    have hm:iteratedDeriv 2 f w≤ iteratedDeriv 2 f z:=hmax hw
    dsimp [η] at hh ⊢
    linarith [hh.2]
  let A:Set ℝ:=Icc a b∩{x|∀z∈Z,δ≤|x-z|}
  have hclosed:IsClosed {x:ℝ|∀z∈Z,δ≤|x-z|}:=by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun z=>isClosed_iInter (fun _=>isClosed_le continuous_const
      ((continuous_id.sub continuous_const).abs)))
  have hcompact:IsCompact A:=isCompact_Icc.inter_right hclosed
  have hc0:ContinuousOn f (Icc a b):=fun x hx=>(hf x hx).continuousAt.continuousWithinAt
  have hc:ContinuousOn f A:=hc0.mono inter_subset_left
  have ha:∀x∈A,f x<0:=by
    intro x hx
    apply hstrict x hx.1
    intro hxZ
    have hh:=hx.2 x hxZ
    simp only [sub_self,abs_zero] at hh
    exact not_le_of_gt hδ hh
  have hmargin:∃ε:ℝ,0<ε ∧ ∀x∈A,f x≤-ε:=by
    by_cases hA:A.Nonempty
    · obtain ⟨x,hx,hM⟩:=hcompact.exists_isMaxOn hA hc
      exact ⟨-f x,neg_pos.mpr (ha x hx),fun y hy=>by simpa only [neg_neg] using (show f y≤f x from hM hy)⟩
    · exact ⟨1,by norm_num,fun x hx=>False.elim (hA ⟨x,hx⟩)⟩
  obtain ⟨ε,hε,hbound⟩:=hmargin
  exact ⟨{
    smooth:=hf,centers:=hz,value_zero:=hzero,slope_zero:=hslope,
    radius:=δ,radius_pos:=hδ,curvature:=η,curvature_pos:=hη,
    margin:=ε,margin_pos:=hε,local_bound:=hlocal,
    away_bound:=fun x hx hfar=>hbound x ⟨hx,hfar⟩}⟩

end polyak.ModeLocking.Analysis
