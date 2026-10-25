import polyak.Farey.Combs.Criterion
import polyak.Farey.Combs.Spines

/-! Construct the comb data directly from the source curve and its
coprime anchor. The inverse multiplier and every sign premise are derived. -/
noncomputable section
namespace polyak.Farey
open Levels MeasureTheory

def Comb.ofCurve (Θ : Curve) (k j i t : ℤ) (hk : 0 < k) (hj : 2≤j)
    (hjk : 2*j < k) (hi : 0 < i) (hik : 2*i < k) (hij : i≠j)
    (ht : 2≤t) (htj : t≤j) (hcop : Int.gcd j k=1)
    (hlo : (t:ℝ)-1 < gridPhase Θ k j hk (by omega) hjk.le)
    (hup : gridPhase Θ k j hk (by omega) hjk.le≤t)
    (hout : (i:ℝ) < gridPhase Θ k i hk hi.le hik.le) : Comb Θ := by
  let b := Int.gcdA j k
  let τ := (i*b)%k
  have he : j*b+k*Int.gcdB j k=1 := by
    simpa only [b,hcop,Nat.cast_one] using (Int.gcd_eq_gcd_ab j k).symm
  have hv : i*b=(i*b/k)*k+τ := (Int.ediv_mul_add_emod (i*b) k).symm
  have htrans : k∣i-τ*j := by
    refine ⟨i*Int.gcdB j k+j*(i*b/k),?_⟩
    linear_combination -i*he+j*hv
  exact {
    data := {
      k:=k,j:=j,i:=i,t:=t,τ:=τ
      a:=gridPhase Θ k j hk (by omega) hjk.le
      ac:=gridPhase Θ k i hk hi.le hik.le
      k_pos:=hk,j_ge:=hj,j_half:=hjk,i_pos:=hi,i_half:=hik,i_ne:=hij
      t_ge:=ht,t_le:=htj,depth_lower:=hlo,depth_upper:=hup
      companion_out:=hout,companion_le:=gridPhase_le Θ k i hk hi.le hik.le
      transport:=htrans }
    coprime:=hcop
    anchor_phase:=rfl
    companion_phase:=rfl }

theorem CombData.anchor_negative_positions (d : CombData) :
    negativePositions d.positions d.anchorColumn=Finset.Icc 1 (d.t-1) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    have hpt := (d.anchor_negative p hp).mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp).1,by omega⟩
  · intro hp
    obtain ⟨hp0,hpt⟩ := Finset.mem_Icc.mp hp
    have hmem : p∈d.positions := by
      apply Finset.mem_Icc.mpr
      have ht := d.t_le
      have hj := d.j_half
      have hj0 := d.j_ge
      omega
    exact Finset.mem_filter.mpr ⟨hmem,(d.anchor_negative p hmem).mpr (by omega)⟩

theorem CombData.companion_negative_positions (d : CombData) :
    negativePositions d.positions d.companionColumn=
      d.positions.filter (fun p=>1≤residue d.k d.τ p ∧ (residue d.k d.τ p:ℝ) < d.ac) := by
  classical
  ext p
  simp only [negativePositions,Finset.mem_filter,d.companion_negative]

theorem CombData.lowerRatio_pos (d : CombData) (hs : d.Selection) : 0 < d.lowerRatio :=
  lowerMassRatio_pos _ _ _ _ (d.selection_iff.mp hs)

theorem Comb.measure_eq {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal) :
    C.measure w0 wc=(w0:ENNReal)•Measure.dirac C.data.anchorFrequency+
      (wc:ENNReal)•Measure.dirac C.data.companionFrequency := by
  unfold Comb.measure atomicMeasure
  rw [Fintype.sum_bool]
  exact add_comm _ _

private theorem grid_mem {k i : ℤ} (hk : 0 < k) (hi : 0 < i) (hik : 2*i≤k) :
    gridFrequency k i hk hi.le hik∈periodicGrid k.toNat := by
  have hkn : 0 < k.toNat := by omega
  apply (mem_periodicGrid_iff hkn _).mpr
  refine ⟨i,hi,by simpa only [Int.toNat_of_nonneg hk.le] using hik,?_⟩
  have hcast : (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  simp only [gridFrequency_val,hcast]

theorem Comb.measure_carried_grid {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal) :
    ∀ᵐω∂C.measure w0 wc,ω∈periodicGrid C.data.k.toNat := by
  apply atomicMeasure_carried_grid
  intro b
  cases b
  · exact grid_mem C.data.k_pos (by have h:=C.data.j_ge;omega) C.data.j_half.le
  · exact grid_mem C.data.k_pos C.data.i_pos C.data.i_half.le

theorem Comb.periodic_of_criterion {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal)
    (hw0 : 0 < w0) (hwc : 0 < wc)
    (hr : C.data.Selection ∧ C.data.lowerRatio≤(wc:ℝ)/(w0:ℝ) ∧ (wc:ℝ)/(w0:ℝ)≤C.data.upperRatio)
    (hm : 0≤(w0:ℝ)*Real.cos (Θ C.data.anchorFrequency)+(wc:ℝ)*Real.cos (Θ C.data.companionFrequency)) :
    PeriodicFP Θ C.data.k.toNat :=
  ⟨C.measure w0 wc,(C.twoatom_criterion w0 wc hw0 hwc).mpr ⟨hr,hm⟩,C.measure_carried_grid w0 wc⟩

end polyak.Farey
