import polyak.Global.Sampling.AliasingSeries
import polyak.Global.Sampling.AliasingRepresentatives
import polyak.Global.Sampling.AliasingDecay

/-! Uniform O(L^-2) aliasing, including the zero frequency and every
balanced signed representative of a residue class. -/
noncomputable section
namespace polyak.Global.Sampling
open Set Complex

 theorem summable_fourierCoeff_of_quadratic_decay (h : C(Circle,ℂ)) {C : ℝ}
    (hdecay : ∀n : ℤ,n≠0→‖fourierCoeff h n‖≤C/(n:ℝ)^2) : Summable (fourierCoeff h) := by
  have hp : Summable (fun n : ℤ=>1/(n:ℝ)^2):=Real.summable_one_div_int_pow.mpr (by norm_num)
  have hz := (hasSum_ite_eq (0:ℤ) ‖fourierCoeff h 0‖).summable
  apply ((hp.mul_left C).add hz).of_norm_bounded
  intro n
  by_cases hn : n=0
  · subst n
    simp only [Int.cast_zero,zero_pow (by norm_num : 2≠0),div_zero,mul_zero,ite_true,zero_add,le_refl]
  · have hh:=hdecay n hn
    simp only [ite_eq_right hn,add_zero]
    convert hh using 1
    ring

def inverseSquareSum : ℝ:=∑'m : ℤ,1/(m:ℝ)^2

theorem inverseSquareSum_nonneg : 0 ≤ inverseSquareSum:=tsum_nonneg (fun _=>by positivity)

 theorem alias_term_bound {C : ℝ} (hC : 0≤C) {L : ℕ} (hL : 0<L) {n m : ℤ}
    (hn : 2*|n|≤(L:ℤ)) (hm : m≠0) :
    C/(((m*(L:ℤ)-n:ℤ):ℝ))^2≤(4*C/(L:ℝ)^2)*(1/(m:ℝ)^2) := by
  have hsep:=alias_separation hL hn hm
  have hmR : (m:ℝ)≠0:=Int.cast_ne_zero.mpr hm
  have hLR : (L:ℝ)≠0:=by exact_mod_cast hL.ne'
  have hsmall : 0<(L:ℝ)*|(m:ℝ)|/2:=by positivity
  have hsquare : ((L:ℝ)*|(m:ℝ)|/2)^2≤|(((m*(L:ℤ)-n:ℤ):ℝ))|^2:=by gcongr
  rw [div_pow,mul_pow,sq_abs,sq_abs] at hsquare
  have hden : 0<(L:ℝ)^2*(m:ℝ)^2/(2:ℝ)^2:=by positivity
  have hh:=div_le_div_of_nonneg_left hC hden hsquare
  calc
    _ ≤ C/((L:ℝ)^2*(m:ℝ)^2/(2:ℝ)^2) := hh
    _ = _ := by field_simp; ring

theorem aliasing_error_le (h : C(Circle,ℂ)) {C : ℝ} (hC : 0≤C)
    (hdecay : ∀n : ℤ,n≠0→‖fourierCoeff h n‖≤C/(n:ℝ)^2)
    {L : ℕ} (hL : 0<L) {n : ℤ} (hn : 2*|n|≤(L:ℤ)) :
    ‖sampleAverage h L n-fourierCoeff h (-n)‖≤(4*C*inverseSquareSum)/(L:ℝ)^2 := by
  have hs:=summable_fourierCoeff_of_quadratic_decay h hdecay
  let f : ℤ→ℂ:=fun m=>fourierCoeff h (m*(L:ℤ)-n)
  let tail : ℤ→ℂ:=fun m=>if m=0 then 0 else f m
  have hfinj : Function.Injective (fun m : ℤ=>m*(L:ℤ)-n) := by
    intro a b he
    have hh : a*(L:ℤ)=b*(L:ℤ):=by linarith
    exact mul_right_cancel₀ (by exact_mod_cast hL.ne' : (L:ℤ)≠0) hh
  have hf : Summable f:=hs.comp_injective hfinj
  have hdecomp : sampleAverage h L n-fourierCoeff h (-n)=∑'m : ℤ,tail m := by
    rw [sampleAverage_aliasing h hs hL n]
    have hh:=hf.tsum_eq_add_tsum_ite (0:ℤ)
    simp only [f,zero_mul,zero_sub] at hh
    dsimp only [tail,f]
    rw [hh]
    ring
  have hterm : ∀m : ℤ,‖tail m‖≤(4*C/(L:ℝ)^2)*(1/(m:ℝ)^2) := by
    intro m
    by_cases hm : m=0
    · subst m
      simp only [tail,ite_true,norm_zero,Int.cast_zero,zero_pow (by norm_num : 2≠0),div_zero,mul_zero,le_refl]
    · have hsep:=alias_separation hL hn hm
      have hmR : (m:ℝ)≠0:=Int.cast_ne_zero.mpr hm
      have hpos : 0 < |(((m*(L:ℤ)-n:ℤ):ℝ))|:=lt_of_lt_of_le (by positivity) hsep
      have hneq : m*(L:ℤ)-n≠0:=by
        intro he
        rw [he,Int.cast_zero,abs_zero] at hpos
        exact lt_irrefl _ hpos
      change ‖if m=0 then 0 else f m‖≤_
      rw [ite_eq_right hm]
      exact (hdecay _ hneq).trans (alias_term_bound hC hL hn hm)
  have hp : Summable (fun m : ℤ=>(4*C/(L:ℝ)^2)*(1/(m:ℝ)^2)):=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1<2)).mul_left _
  have ht : Summable (fun m : ℤ=>‖tail m‖):=hp.of_nonneg_of_le (fun _=>norm_nonneg _) hterm
  rw [hdecomp]
  calc
    _ ≤ ∑'m : ℤ,‖tail m‖:=norm_tsum_le_tsum_norm ht
    _ ≤ ∑'m : ℤ,(4*C/(L:ℝ)^2)*(1/(m:ℝ)^2):=ht.tsum_le_tsum hterm hp
    _ = (4*C*inverseSquareSum)/(L:ℝ)^2 := by rw [tsum_mul_left]; unfold inverseSquareSum; ring

 theorem exists_aliasing_error_bound (h : C(Circle,ℂ)) {C : ℝ} (hC : 0≤C)
    (hdecay : ∀n : ℤ,n≠0→‖fourierCoeff h n‖≤C/(n:ℝ)^2) :
    ∃K : ℝ,0≤K ∧ ∀L : ℕ,0<L→∀n : ℤ,2*|n|≤(L:ℤ)→
      ‖sampleAverage h L n-fourierCoeff h (-n)‖≤K/(L:ℝ)^2 := by
  exact ⟨4*C*inverseSquareSum,by positivity [inverseSquareSum_nonneg],
    fun _ hL _ hn=>aliasing_error_le h hC hdecay hL hn⟩

end polyak.Global.Sampling
