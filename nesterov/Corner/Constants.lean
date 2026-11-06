import nesterov.TwoStep.Band
import nesterov.Flow.Constants
import Mathlib.Topology.Compactness.Compact

/-! The literal minima in the corner theorem, including its compact discrete set. -/
namespace nesterov.Corner
noncomputable section
open Set Filter
open scoped Topology

def N (θ a b ξ : ℝ) : ℝ :=
  4*θ+2*(θ-4*a)*ξ+2*(4*a+b-2*θ)*ξ^2

def ratio (θ a b ξ : ℝ) : ℝ := N θ a b ξ/(4*(3-ξ))
def cpi (θ a b : ℝ) : ℝ := 2*(2*a+b-θ)
def rationalXi (K : ℕ) : ℝ := 1-Real.cos (2*Real.pi/K)
def discreteSet : Set ℝ := insert 2 (insert 0 (Set.range (fun n : ℕ=>rationalXi (n+3))))
def cLag (θ a b : ℝ) : ℝ := sInf (ratio θ a b '' Icc 0 2)
def cDisc (θ a b : ℝ) : ℝ := sInf (ratio θ a b '' discreteSet)

theorem ratio_zero (θ a b : ℝ) : ratio θ a b 0=θ/3 := by simp [ratio,N];ring

theorem ratio_two (θ a b : ℝ) : ratio θ a b 2=cpi θ a b := by
  unfold ratio N cpi
  norm_num
  ring

theorem ratio_continuousOn (θ a b : ℝ) : ContinuousOn (ratio θ a b) (Icc 0 2) := by
  apply ContinuousOn.div (by unfold N;fun_prop) (by fun_prop)
  intro x hx
  have : 0<4*(3-x) := by nlinarith [hx.2]
  exact this.ne'

theorem rationalXi_mem (K : ℕ) : rationalXi K∈Icc 0 2 := by
  constructor
  · exact sub_nonneg.mpr (Real.cos_le_one _)
  · have := Real.neg_one_le_cos (2*Real.pi/K)
    unfold rationalXi
    linarith

theorem rationalXi_tendsto : Tendsto (fun n : ℕ=>rationalXi (n+3)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ=>(n:ℝ)+3) atTop atTop :=
    by simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 3)
  have hangle : Tendsto (fun n : ℕ=>2*Real.pi/((n:ℝ)+3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have ht := Real.continuous_cos.continuousAt.tendsto.comp hangle
  have h := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub ht
  convert h using 1 <;> simp [rationalXi,Nat.cast_add,Nat.cast_ofNat]

theorem discreteSet_compact : IsCompact discreteSet :=
  rationalXi_tendsto.isCompact_insert_range.insert 2

theorem discreteSet_subset : discreteSet⊆Icc 0 2 := by
  intro x hx
  rcases hx with rfl|rfl|⟨n,rfl⟩
  · norm_num
  · norm_num
  · exact rationalXi_mem _

theorem zero_mem_discreteSet : (0:ℝ)∈discreteSet := by simp [discreteSet]
theorem two_mem_discreteSet : (2:ℝ)∈discreteSet := by simp [discreteSet]

theorem rationalXi_mem_discreteSet {K : ℕ} (hK : 3≤K) : rationalXi K∈discreteSet := by
  have : K=(K-3)+3 := by omega
  rw [this]
  exact Or.inr (Or.inr ⟨K-3,rfl⟩)

theorem discreteSet_iff {x : ℝ} : x∈discreteSet ↔
    x=0 ∨ x=2 ∨ ∃ K : ℕ,3≤K ∧ x=rationalXi K := by
  constructor
  · rintro (rfl|rfl|⟨n,rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨n+3,by omega,rfl⟩)
  · rintro (rfl|rfl|⟨K,hK,rfl⟩)
    · exact zero_mem_discreteSet
    · exact two_mem_discreteSet
    · exact rationalXi_mem_discreteSet hK

theorem cLag_attained (θ a b : ℝ) : ∃ ξ∈Icc (0:ℝ) 2,ratio θ a b ξ=cLag θ a b := by
  obtain ⟨ξ,hξ,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤2))
    (ratio_continuousOn θ a b)
  refine ⟨ξ,hξ,?_⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_,ξ,hξ,rfl⟩
    · rintro v ⟨x,hx,rfl⟩
      exact hmin hx
  · exact csInf_le (isCompact_Icc.image_of_continuousOn (ratio_continuousOn θ a b)).bddBelow
      ⟨ξ,hξ,rfl⟩

theorem cDisc_attained (θ a b : ℝ) : ∃ ξ∈discreteSet,ratio θ a b ξ=cDisc θ a b := by
  obtain ⟨ξ,hξ,hmin⟩ := discreteSet_compact.exists_isMinOn ⟨0,zero_mem_discreteSet⟩
    ((ratio_continuousOn θ a b).mono discreteSet_subset)
  refine ⟨ξ,hξ,?_⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_,ξ,hξ,rfl⟩
    · rintro v ⟨x,hx,rfl⟩
      exact hmin hx
  · exact csInf_le (discreteSet_compact.image_of_continuousOn
      ((ratio_continuousOn θ a b).mono discreteSet_subset)).bddBelow ⟨ξ,hξ,rfl⟩

theorem cLag_le {θ a b ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) : cLag θ a b≤ratio θ a b ξ :=
  csInf_le (isCompact_Icc.image_of_continuousOn (ratio_continuousOn θ a b)).bddBelow ⟨ξ,hξ,rfl⟩

theorem cDisc_le {θ a b ξ : ℝ} (hξ : ξ∈discreteSet) : cDisc θ a b≤ratio θ a b ξ :=
  csInf_le (discreteSet_compact.image_of_continuousOn
    ((ratio_continuousOn θ a b).mono discreteSet_subset)).bddBelow ⟨ξ,hξ,rfl⟩

theorem le_cLag {θ a b c : ℝ} (h : ∀ ξ∈Icc (0:ℝ) 2,c≤ratio θ a b ξ) : c≤cLag θ a b := by
  apply le_csInf
  · exact ⟨_,0,by norm_num,rfl⟩
  · rintro v ⟨ξ,hξ,rfl⟩
    exact h ξ hξ

theorem le_cDisc {θ a b c : ℝ} (h : ∀ ξ∈discreteSet,c≤ratio θ a b ξ) : c≤cDisc θ a b := by
  apply le_csInf
  · exact ⟨_,0,zero_mem_discreteSet,rfl⟩
  · rintro v ⟨ξ,hξ,rfl⟩
    exact h ξ hξ

theorem cLag_le_cDisc (θ a b : ℝ) : cLag θ a b≤cDisc θ a b := by
  apply le_cDisc
  intro ξ hξ
  exact cLag_le (discreteSet_subset hξ)

theorem cDisc_endpoints (θ a b : ℝ) : cDisc θ a b≤min (θ/3) (cpi θ a b) := by
  apply le_min
  · simpa only [ratio_zero] using (cDisc_le (θ:=θ) (a:=a) (b:=b) zero_mem_discreteSet)
  · simpa only [ratio_two] using (cDisc_le (θ:=θ) (a:=a) (b:=b) two_mem_discreteSet)

theorem cpi_pos_iff {θ a b : ℝ} : 0<cpi θ a b ↔ θ<2*a+b := by
  unfold cpi
  constructor <;> intro h <;> linarith

theorem cLag_eq_cDisc_of_mem_min {θ a b ξ : ℝ} (hξ : ξ∈discreteSet)
    (hmin : ratio θ a b ξ=cLag θ a b) : cLag θ a b=cDisc θ a b :=
  le_antisymm (cLag_le_cDisc _ _ _) (hmin ▸ cDisc_le hξ)

end
end nesterov.Corner
