import nesterov.Slow.FastRoots
import nesterov.IQC.MiddleRadius

/-! A strictly stable limit middle polynomial gives one uniform fast-mode gap. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

def middlePolynomial (ε : ℝ) : Polynomial ℂ := (F.method ε).characteristicPolynomial ((1+ε^2)/2)

theorem middlePolynomial_degree (ε : ℝ) : (F.middlePolynomial ε).natDegree=F.memory := by
  rw [middlePolynomial,(F.method ε).characteristicPolynomial_natDegree,F.fixed_memory]

theorem middlePolynomial_coeff_limit (j : ℕ) :
    Tendsto (fun ε=>(F.middlePolynomial ε).coeff j) (𝓝[>] (0:ℝ))
      (𝓝 ((F.middlePolynomial 0).coeff j)) := by
  simp only [middlePolynomial,StationaryMethod.characteristicPolynomial_eq_source,
    Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_map]
  have hc (x : ℝ) : Complex.ofRealHom x=(x:ℂ) := rfl
  simp only [hc]
  have hu := (Complex.continuous_ofReal.tendsto _).comp (F.u_coeff_tendsto j)
  have hv := (Complex.continuous_ofReal.tendsto _).comp (F.v_coeff_tendsto j)
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hlamr : Tendsto (fun ε : ℝ=>(1+ε^2)/2) (𝓝[>] (0:ℝ)) (𝓝 (1/2:ℝ)) := by
    simpa only [zero_pow (by decide : 2≠0),add_zero] using ((he.pow 2).const_add 1).div_const 2
  have hlam := (Complex.continuous_ofReal.tendsto (1/2:ℝ)).comp hlamr
  convert hv.sub (hlam.mul hu) using 1 <;> simp [SecondOrderFamily.u,SecondOrderFamily.v]

/-- A fixed radius less than one contains every nearby middle-quadratic root. -/
theorem middle_uniform_gap
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1) :
    ∃ r : ℝ,0<r ∧ r<1 ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∀ z : ℂ,(F.middlePolynomial ε).eval z=0 → ‖z‖<r := by
  let p₀ := F.middlePolynomial 0
  have hp₀ : p₀≠0 := by
    intro h
    have hd := F.middlePolynomial_degree 0
    change p₀.natDegree=F.memory at hd
    rw [h,Polynomial.natDegree_zero] at hd
    have hm := F.memory_two
    omega
  have hfin : Set.Finite {z : ℂ | p₀.eval z=0} := Polynomial.finite_setOfPred_isRoot hp₀
  have hnon : ({z : ℂ | p₀.eval z=0} : Set ℂ).Nonempty := by
    obtain ⟨_,z,hz,_⟩ := (IQC.middleRootNorms_nonempty (F.method 0) 0 1)
    refine ⟨z,?_⟩
    change p₀.eval z=0
    simpa only [p₀,middlePolynomial,zero_pow (by decide : 2≠0),add_zero,
      StationaryMethod.characteristicPolynomial_eval] using hz
  obtain ⟨z₀,hz₀,hmax⟩ := hfin.isCompact.exists_isMaxOn hnon continuous_norm.continuousOn
  let r := (1+‖z₀‖)/2
  have hr : 0<r := by dsimp [r];linarith [norm_nonneg z₀]
  have hr1 : r<1 := by dsimp [r];linarith [hs z₀ hz₀]
  refine ⟨r,hr,hr1,?_⟩
  apply nesterov.Slow.roots_eventually_lt F.middlePolynomial_degree (F.middlePolynomial_degree 0) hp₀ F.middlePolynomial_coeff_limit
  intro z hz
  have hh : ‖z‖≤‖z₀‖ := hmax hz
  dsimp [r]
  linarith [hs z₀ hz₀]

/-- The exact threshold needed by the one-exponent principle, for every
fixed slow exponent c, follows from strict stability of the limit polynomial. -/
theorem middleRadius_lt_exp
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1) (c : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),IQC.middleRadius (F.method ε) (ε^2) 1<Real.exp (-c*ε) := by
  obtain ⟨r,_,hr1,hroots⟩ := F.middle_uniform_gap hs
  have hεlim : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have he : Tendsto (fun ε : ℝ=>Real.exp (-c*ε)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hm : Tendsto (fun ε : ℝ=> -c*ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using hεlim.const_mul (-c)
    simpa only [Real.exp_zero,Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hm
  have hr := he.eventually (eventually_gt_nhds hr1)
  have hsmall := hεlim.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hroots,hr,hsmall,self_mem_nhdsWithin] with ε hroot hrε hε1 hε0
  have hε : 0<ε := hε0
  have hμL : ε^2<1 := by nlinarith
  obtain ⟨z,hz,heq⟩ := (IQC.middleRadius_isGreatest (F.method ε) (sq_pos_of_pos hε) hμL).1
  rw [heq]
  exact (hroot z (by simpa only [middlePolynomial,StationaryMethod.characteristicPolynomial_eval] using hz)).trans hrε

end
end nesterov.Slow.SecondOrderFamily
