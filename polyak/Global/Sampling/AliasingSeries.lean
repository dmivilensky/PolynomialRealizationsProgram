import polyak.Global.Sampling.AliasingGrid

/-! The exact aliasing formula for the genuine equally spaced samples of
any absolutely convergent official Fourier series on the source circle. -/
noncomputable section
namespace polyak.Global.Sampling
open Set Complex
open scoped BigOperators

def sampleAverageCLM (L : ℕ) (n : ℤ) : C(Circle,ℂ)→L[ℂ]ℂ :=
  (L:ℂ)⁻¹ • ∑j : Fin L,fourier n (samplePoint L j) • ContinuousMap.evalCLM ℂ (samplePoint L j)

@[simp] theorem sampleAverageCLM_apply (h : C(Circle,ℂ)) (L : ℕ) (n : ℤ) :
    sampleAverageCLM L n h=sampleAverage h L n := by
  simp only [sampleAverageCLM,smul_apply,sum_apply,
    smul_eq_mul,ContinuousMap.evalCLM_apply,sampleAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sampleAverage_fourier {L : ℕ} (hL : 0<L) (k n : ℤ) :
    sampleAverage (fourier k) L n=if (L:ℤ)∣k+n then 1 else 0 := by
  unfold sampleAverage
  simp_rw [←fourier_add]
  exact average_fourier_samplePoint hL (k+n)

theorem hasSum_alias_indicator (h : C(Circle,ℂ)) (hs : Summable (fourierCoeff h))
    {L : ℕ} (hL : 0<L) (n : ℤ) :
    HasSum (fun k : ℤ=>if (L:ℤ)∣k+n then fourierCoeff h k else 0) (sampleAverage h L n) := by
  have hh:=(sampleAverageCLM L n).hasSum (hasSum_fourier_series_of_summable hs)
  convert hh using 1
  · funext k
    rw [map_smul,smul_eq_mul,sampleAverageCLM_apply,sampleAverage_fourier hL]
    split_ifs <;> simp only [mul_one,mul_zero]
  · exact (sampleAverageCLM_apply h L n).symm

def aliasEquiv (L : ℕ) (hL : 0<L) (n : ℤ) :
    ℤ≃{k : ℤ // (L:ℤ)∣k+n} where
  toFun m:=⟨m*L-n,⟨m,by ring⟩⟩
  invFun k:=(k.val+n)/L
  left_inv m:=by
    simp only [sub_add_cancel]
    exact Int.mul_ediv_cancel m (by exact_mod_cast hL.ne')
  right_inv k:=by
    apply Subtype.ext
    have hh:=Int.ediv_mul_cancel k.property
    dsimp
    linarith

theorem sampleAverage_aliasing (h : C(Circle,ℂ)) (hs : Summable (fourierCoeff h))
    {L : ℕ} (hL : 0<L) (n : ℤ) :
    sampleAverage h L n=∑'m : ℤ,fourierCoeff h (m*(L:ℤ)-n) := by
  have hh:=(hasSum_alias_indicator h hs hL n).tsum_eq
  have hsub : (∑'k : {k : ℤ // (L:ℤ)∣k+n},fourierCoeff h k.val)=sampleAverage h L n := by
    calc
      _ = ∑'k : ℤ,({k : ℤ | (L:ℤ)∣k+n}:Set ℤ).indicator (fourierCoeff h) k :=
        tsum_subtype {k : ℤ | (L:ℤ)∣k+n} (fourierCoeff h)
      _ = _ := by simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using hh
  rw [←hsub]
  exact ((aliasEquiv L hL n).tsum_eq (fun k=>fourierCoeff h k.val)).symm

end polyak.Global.Sampling
