import nesterov.Phase.Algebra
import nesterov.Closure.Equality
import polyak.General.Multipliers.Certificates

/-!
Article: Proposition `prop:lagone`, including strictification at z=1.
Use: genuine finite certificates, preserving the exact common-value cancellation.
-/
namespace nesterov.Phase
noncomputable section
open Spectral Duality Set
open scoped BigOperators

/-- Uniformize a negative continuous finite spectral symbol. -/
theorem certificate_of_negative (a : SymbolPair) (t : ℝ) (s : Finset ℕ)
    (α β : ℕ→ℝ) (gp gm : ℝ) (hs : ∀ n∈s,1≤n)
    (hα : ∀ n∈s,0≤α n) (hβ : ∀ n∈s,0≤β n) (hgp : 0≤gp) (hgm : 0≤gm)
    (hc : (∑ n∈s,(α n-β n)*Real.sinh (n*t))+gp-gm=0)
    (hneg : ∀ c,symbol a t s α β gp gm c<0) : Nonempty (Duality.StrictCertificate a t) := by
  let : Nonempty Frequency := ⟨⟨0,by norm_num,by norm_num⟩⟩
  obtain ⟨c,_,hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    (continuous_symbol a t s α β gp gm).continuousOn
  exact ⟨⟨s,hs,α,β,hα,hβ,gp,gm,hgp,hgm,-symbol a t s α β gp gm c,
    neg_pos.mpr (hneg c),hc,fun y=>by rw [neg_neg]; exact hmax (mem_univ y)⟩⟩

def lagOne (a : SymbolPair) (t : ℝ) (c : Frequency) : ℝ :=
  (((g a c:ℝ):ℂ)-2*Complex.I*skew a c)*
    (1-polyak.Waves.z t (Real.arccos c)) |>.re

theorem lagOne_symbol (a : SymbolPair) (t : ℝ) (c : Frequency) :
    symbol a t {1} (fun n=>if n=1 then Real.exp t else 0) (fun _=>0)
      (-Real.exp t*Real.sinh t) 0 c=lagOne a t c := by
  have he : Real.exp t*(Real.cosh t-Real.sinh t)=1 := by
    rw [Real.cosh_sub_sinh,←Real.exp_add]
    simp
  simp only [symbol,Finset.sum_singleton,ite_eq_left,zero_mul,add_zero,lagA,lagB,
    lagOne,Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  norm_num
  have hre : (polyak.Waves.z t (Real.arccos c)).re=Real.exp t*Real.cos (Real.arccos c) := by
    simpa using polyak.Waves.z_pow_re t (Real.arccos c) 1
  have him : (polyak.Waves.z t (Real.arccos c)).im=Real.exp t*Real.sin (Real.arccos c) := by
    simpa using polyak.Waves.z_pow_im t (Real.arccos c) 1
  rw [hre,him]
  linear_combination (g a c)*he

theorem continuous_lagOne (a : SymbolPair) (t : ℝ) : Continuous (lagOne a t) := by
  unfold lagOne g skew polyak.Waves.z
  fun_prop

/-- The source lag-one weights are nonnegative precisely on t≤0. -/
theorem lagOne_certificate {a : SymbolPair} {t : ℝ} (ht : t≤0)
    (hneg : ∀ c,lagOne a t c<0) : Nonempty (Duality.StrictCertificate a t) := by
  apply certificate_of_negative a t {1} (fun n=>if n=1 then Real.exp t else 0)
    (fun _=>0) (-Real.exp t*Real.sinh t) 0
  · simp
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    simpa using (Real.exp_pos t).le
  · simp
  · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Real.exp_pos t).le) (Real.sinh_nonpos_iff.mpr ht)
  · norm_num
  · simp
  · intro c
    simpa only [lagOne_symbol] using hneg c

/-- Exact link to the original endpoint polynomials, with its positive factor. -/
theorem lagOne_momentum {μ L β τ h : ℝ} (hμL : μ<L) (hh : h≠0)
    (t : ℝ) (c : Frequency) :
    lagOne ((Momentum.method β τ h hh).symbolPair μ L t) t c=
      -(4/(h^2*(L-μ)^2))*
        ((1-polyak.Waves.z t (Real.arccos c))*
          Quadratic.characteristic β τ h μ (polyak.Waves.z t (Real.arccos c))*
          star (Quadratic.characteristic β τ h L (polyak.Waves.z t (Real.arccos c)))).re := by
  unfold lagOne
  rw [momentum_factor hμL hh]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im]
  ring

/-- Proposition lagone(a), in the exact exponential threshold convention. -/
theorem momentumRate_lt_of_lagOne (q : Momentum.Tuning) {μ L t : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (ht : t≤0)
    (hr : IQC.middleRadius (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L<Real.exp t)
    (hpos : ∀ z : ℂ,‖z‖=Real.exp t →
      0<((1-z)*Quadratic.characteristic q.beta q.tau q.stepSize μ z*
        star (Quadratic.characteristic q.beta q.tau q.stepSize L z)).re) :
    Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<Real.exp t := by
  obtain ⟨cert⟩ := lagOne_certificate ht (a:=(Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)
    (fun c=>by
      rw [lagOne_momentum hμL q.step_pos.ne']
      have hp := hpos (polyak.Waves.z t (Real.arccos c))
        (by simpa using polyak.Waves.norm_z_pow t (Real.arccos c) 1)
      have hd : 0<4/(q.stepSize^2*(L-μ)^2) :=
        div_pos (by norm_num) (mul_pos (pow_pos q.step_pos _) (pow_pos (sub_pos.mpr hμL) _))
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hp)
  exact IQC.one_exponent hμ hμL hr cert

end
end nesterov.Phase
