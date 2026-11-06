import nesterov.Slow.Roots

/-! Persistence of fixed limiting characteristic roots under continuous coefficients. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

theorem characteristic_tendsto (lam : ℝ) (z : ℂ) :
    Tendsto (fun ε=>(F.method ε).characteristic lam z) (𝓝[>] (0:ℝ))
      (𝓝 ((F.method 0).characteristic lam z)) := by
  have hu := F.u_eval_tendsto (z:=fun _=>z) tendsto_const_nhds
  have hv := F.v_eval_tendsto (z:=fun _=>z) tendsto_const_nhds
  have hh := hv.sub (hu.const_mul (lam:ℂ))
  simpa only [StationaryMethod.characteristic_eq_polynomial_eval,eval_sub,eval_mul,eval_C,eval_map] using hh

theorem fixed_root_near {lam : ℝ} (hlam : lam≠0) {z₀ : ℂ}
    (hz₀ : (F.method 0).characteristic lam z₀=0) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ z : ℂ,(F.method ε).characteristic lam z=0 ∧ ‖z-z₀‖<δ := by
  have hd (ε : ℝ) : ((F.method ε).characteristicPolynomial lam).natDegree≤F.memory := by
    rw [(F.method ε).characteristicPolynomial_natDegree,F.fixed_memory]
  have he (z : ℂ) : Tendsto (fun ε=>((F.method ε).characteristicPolynomial lam).eval z)
      (𝓝[>] (0:ℝ)) (𝓝 (((F.method 0).characteristicPolynomial lam).eval z)) := by
    simpa only [StationaryMethod.characteristicPolynomial_eval] using F.characteristic_tendsto lam z
  have hp : (F.method 0).characteristicPolynomial lam≠0 := by
    intro hp
    have hh := congrArg (Polynomial.eval (1:ℂ)) hp
    simp only [StationaryMethod.characteristicPolynomial_eval,StationaryMethod.characteristic_one,eval_zero] at hh
    exact (Complex.ofReal_ne_zero.mpr hlam) (neg_eq_zero.mp hh)
  have hroot : ((F.method 0).characteristicPolynomial lam).eval z₀=0 := by
    rwa [StationaryMethod.characteristicPolynomial_eval]
  simpa only [StationaryMethod.characteristicPolynomial_eval] using
    nesterov.Slow.eventually_exists_root_near hd he hp hroot hδ

theorem fixed_unstable_root_lower {lam : ℝ} (hlam : lam∈Ioo (0:ℝ) 1) {z₀ : ℂ}
    (hz₀ : (F.method 0).characteristic lam z₀=0) (hn₀ : 1<‖z₀‖) :
    ∃ r : ℝ,1<r ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ z : ℂ,(F.method ε).characteristic lam z=0 ∧ r<‖z‖ ∧
        r<nesterov.Rates.quadraticRate (F.method ε) (ε^2) 1 := by
  let r := (1+‖z₀‖)/2
  have hr : 1<r := by dsimp [r];linarith
  have hδ : 0<(‖z₀‖-1)/2 := by linarith
  have he : Tendsto (fun ε : ℝ=>ε^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (continuous_id.continuousWithinAt.tendsto : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0)).pow 2
  have hμlam := he.eventually (eventually_lt_nhds hlam.1)
  refine ⟨r,hr,?_⟩
  filter_upwards [F.fixed_root_near hlam.1.ne' hz₀ hδ,hμlam,self_mem_nhdsWithin] with ε hε hμ hp
  change 0<ε at hp
  obtain ⟨z,hz,hnear⟩ := hε
  have htri := norm_le_norm_sub_add z₀ z
  rw [norm_sub_rev] at htri
  have hn : r<‖z‖ := by dsimp [r];linarith
  have hμL : ε^2<1 := hμ.trans hlam.2
  have hrate : ‖z‖≤nesterov.Rates.quadraticRate (F.method ε) (ε^2) 1 :=
    (nesterov.Rates.quadraticRate_isGreatest (F.method ε) (sq_pos_of_pos hp) hμL).2
      ⟨lam,⟨hμ.le,hlam.2.le⟩,z,hz,rfl⟩
  exact ⟨z,hz,hn,hn.trans_le hrate⟩

end
end nesterov.Slow.SecondOrderFamily
