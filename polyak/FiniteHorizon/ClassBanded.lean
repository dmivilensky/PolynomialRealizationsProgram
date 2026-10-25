import polyak.FiniteHorizon.ClassPlateau
import polyak.FiniteHorizon.BandedEstimate
import polyak.Energy.Circle

/-!
Article: Appendix C, Lemma plateauclass for arbitrary finite banded functionals.
Use: Fourier localization and exact zero-charge cancellation give the finite
energy estimate directly. Neither a spectral factor nor continuation of the
restriction-closed class is assumed. Integer offsets are absorbed in the center.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Filter Set Finset
open scoped Topology

def segmentDiscountedValue {A B β : ℝ} {H d n : ℕ}
    (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n) (t : ℝ) (k : ℕ) : ℝ:=
  if 1≤k ∧ k≤n then Real.exp (-2*(k : ℝ)*t)*s.value k else 0

theorem abs_segmentDiscountedValue_le {A B β : ℝ} {H d n : ℕ}
    (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n) (t : ℝ) (k : ℕ) :
    |segmentDiscountedValue s t k|≤discountedEnergy s.x t k/2 := by
  unfold segmentDiscountedValue
  split_ifs with hk
  · rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    have hh:=mul_le_mul_of_nonneg_left (s.abs_value_le k hk.1 hk.2) (Real.exp_pos (-2*(k : ℝ)*t)).le
    simpa only [discountedEnergy,mul_div_assoc] using hh
  · simp only [abs_zero]
    exact div_nonneg (discountedEnergy_nonneg s.x t k) (by norm_num)

namespace SegmentClass
variable {A B β : ℝ} {H : ℕ} (G : SegmentClass A B β H)

def BandedNonnegative (t : ℝ) (K : Kernel) (S : Finset ℕ) (d : ℕ → ℝ) (N : ℕ) : Prop:=
  ∀ D n : ℕ,∀ s : HSegment (EuclideanSpace ℝ (Fin D)) A B β H n,G.contains D n s →
    ∀ k : ℕ,N≤k → k+N≤n → 0≤kernelEval K (discountedInteger s.x t) k+
      finiteValueCombination S d (segmentDiscountedValue s t) k

theorem energyBound_of_banded {t ε : ℝ} (K : Kernel) (S : Finset ℕ) (d : ℕ → ℝ)
    (hε : 0<ε) (hneg : ∀ θ,kernelSymbol K θ≤ -ε) (hcharge : ∑ a∈S,d a=0)
    (N : ℕ) (hsource : G.BandedNonnegative t K S d N) :
    ∃ C : ℝ,∃ w : ℕ,0<C ∧ G.EnergyBound t C w := by
  obtain ⟨R,hR,hsupport⟩:=exists_kernel_radius K (max N (S.sup id))
  let w:=2*R
  let M:=kernelSize K+(∑ a∈S,|d a|)/2
  let C:=M/ε+1
  have hM : 0≤M:=add_nonneg (kernelSize_nonneg K) (by positivity)
  have hC : 0<C:=by dsimp [C]; linarith [div_nonneg hM hε.le]
  have hwN : N≤w:=by dsimp [w]; omega
  have hwS : ∀ a∈S,a≤w:=by
    intro a ha
    have hh : a≤S.sup id:=le_sup (f:=id) ha
    dsimp [w]
    omega
  refine ⟨C,w,hC,fun D n s hs i j hi hij hjn => ?_⟩
  let f:=discountedPosition s.x t
  let b:=discountedEnergy s.x t
  have hb : ∀ k,0≤b k:=discountedEnergy_nonneg s.x t
  have hf : (fun k => ‖f k‖^2)=b:=funext (norm_discountedPosition_sq s.x t)
  have hquad:=sum_kernelEval_nat_interval_le K f hneg R hsupport i j hi hij
  rw [hf] at hquad
  have hvalues:=abs_sum_finiteValueCombination_le hcharge hb hij hwS (abs_segmentDiscountedValue_le s t)
  have hsum : 0≤∑ k∈Icc i j,(kernelEval K (discountedInteger s.x t) k+
      finiteValueCombination S d (segmentDiscountedValue s t) k):=by
    apply sum_nonneg
    intro k hk
    apply hsource D n s hs k
    · have hki:=(mem_Icc.mp hk).1
      omega
    · have hkj:=(mem_Icc.mp hk).2
      omega
  rw [sum_add_distrib] at hsum
  change (∑ k∈Icc i j,kernelEval K (discountedInteger s.x t) k)≤_ at hquad
  have hvalup:=(le_abs_self (∑ k∈Icc i j,
    finiteValueCombination S d (segmentDiscountedValue s t) k)).trans hvalues
  have hnorm : ε*(∑ k∈Icc i j,b k)≤M*(window b w i+window b w j):=by
    dsimp [M,w]
    linarith
  have hwin : 0≤window b w i+window b w j:=add_nonneg (window_nonneg hb _ _) (window_nonneg hb _ _)
  have hdiv : (∑ k∈Icc i j,b k)≤(M/ε)*(window b w i+window b w j):=by
    calc
      _≤(M*(window b w i+window b w j))/ε:=(le_div_iff₀ hε).mpr (by nlinarith)
      _=_:=by ring
  have hfinal : (∑ k∈Icc i j,b k)≤C*(window b w i+window b w j):=by
    dsimp [C]
    nlinarith
  simpa only [mass,Ico_add_one_right_eq_Icc,←window_eq_energyWindow] using hfinal

/-- Lemma plateauclass, with its full arbitrary-class quantifiers and the
source's strict inequality on exactly the closed half-circle [0,π]. -/
theorem not_banded_at_rate {r : ℝ} (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r))
    (K : Kernel) (S : Finset ℕ) (d : ℕ → ℝ) (hcharge : ∑ a∈S,d a=0)
    (hstrict : ∀ ω : ℝ,0≤ω → ω≤Real.pi → kernelSymbol K (ω : FrequencyCircle)<0)
    (N : ℕ) (hsource : G.BandedNonnegative (Real.log r) K S d N) : False := by
  have hc : Continuous (fun ω : ℝ => -kernelSymbol K (ω : FrequencyCircle)):=by fun_prop
  obtain ⟨ε,hε,hgap⟩:=isCompact_Icc.exists_forall_le' hc.continuousOn
    (show ∀ ω∈Icc (0 : ℝ) Real.pi,0< -kernelSymbol K (ω : FrequencyCircle) from
      fun ω hω => neg_pos.mpr (hstrict ω hω.1 hω.2))
  have hneg : ∀ θ : FrequencyCircle,kernelSymbol K θ≤ -ε:=by
    apply kernelSymbol_le_of_halfCircle
    intro ω hω0 hωπ
    have hh:=hgap ω ⟨hω0,hωπ⟩
    linarith
  obtain ⟨C,w,hC,henergy⟩:=G.energyBound_of_banded K S d hε hneg hcharge N hsource
  exact G.not_energyBound_at_rate hpos hr hlim hC henergy

end SegmentClass
end polyak.FiniteHorizon
