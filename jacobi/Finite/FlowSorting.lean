import jacobi.Finite.FlowSortingMatrices
import jacobi.Finite.FlowSpectralBounds
import jacobi.Jacobi.FiniteMoments

/-!
Complete sorting and limiting energy of the actual resolvent flow.
Strictly ordered exponential velocities determine the dominant polynomial
atoms. The proved finite matrix sorting theorem gives both diagonal limits;
continuity of the positive endpoint inverse gives their true energies.
Use: the final realization comparison explains why the two infinite-time
Richardson schedules have quartic rather than cubic Jacobi energy.
Article: jacobi, Proposition 5.5 and Section 5.6.
Article role: both sorted matrix limits, limiting Richardson energy and its quartic Jacobi
asymptotic.
-/
namespace jacobi.Finite
noncomputable section
open Real Filter Set Matrix chebyshev2
open scoped Topology BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- The ratio of any two true tilted probabilities is the exact
unnormalized exponential ratio; its partition sum cancels completely.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem tiltWeight_ratio {n : ℕ} (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ)
    (t : ℝ) (i j : Fin (n+1)) :
    tiltWeight w v t i/tiltWeight w v t j=
      (w.val i/w.val j)*exp (t*(v i-v j)) := by
  rw [mul_sub,exp_sub]
  unfold tiltWeight
  field_simp [(tiltNormalizer_pos w v t).ne',(w.property.1 j).ne',exp_ne_zero]

/-- The exact probability ratios vanish in every strict dominance
direction at positive infinite time.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventWeight_ratio_atTop {n : ℕ} (S : Nodes (n+1)) (w : WeightSimplex (n+1))
    (i j : Fin (n+1)) (hij : i < j) :
    Tendsto (fun t : ℝ => (resolventWeights S w t).val i/(resolventWeights S w t).val j)
      atTop (𝓝 0) := by
  simp_rw [resolventWeights_eq_tilt,tiltWeight_ratio]
  have h := tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_const_of_neg
      (sub_neg.mpr (resolventVelocity_strictMono S hij)))
  simpa only [Function.comp_def,id_eq,mul_zero] using h.const_mul (w.val i/w.val j)

/-- The dominance direction reverses at negative infinite time.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventWeight_ratio_atBot {n : ℕ} (S : Nodes (n+1)) (w : WeightSimplex (n+1))
    (i j : Fin (n+1)) (hji : j < i) :
    Tendsto (fun t : ℝ => (resolventWeights S w t).val i/(resolventWeights S w t).val j)
      atBot (𝓝 0) := by
  simp_rw [resolventWeights_eq_tilt,tiltWeight_ratio]
  have h := tendsto_exp_atBot.comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).atBot_mul_const
      (sub_pos.mpr (resolventVelocity_strictMono S hji)))
  simpa only [Function.comp_def,id_eq,mul_zero] using h.const_mul (w.val i/w.val j)

/-- At positive infinite time the actual full Jacobi matrix tends to
the roots in increasing physical order, with every momentum link vanishing.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventFlow_atTop {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    Tendsto (fun t : ℝ => (resolventFlow S J t).val.matrix) atTop
      (𝓝 (diagonal (fun i => S.value i.rev))) := by
  have h := reconstructed_matrix_sorting (flowMeasure S (spectralWeights S J)) S.value
    (fun _ => rfl) Fin.revPerm (fun j k hjk =>
      resolventWeight_ratio_atTop S (spectralWeights S J) k.rev j.rev
        (Fin.rev_lt_rev.mpr hjk))
  exact h

/-- At negative infinite time the roots occur in descending physical
order. This proves the second full matrix limit, beyond weight concentration.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventFlow_atBot {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    Tendsto (fun t : ℝ => (resolventFlow S J t).val.matrix) atBot
      (𝓝 (diagonal S.value)) := by
  have h := reconstructed_matrix_sorting (fun t => flowMeasure S (spectralWeights S J) (-t)) S.value
    (fun _ => rfl) (Equiv.refl _) (fun j k hjk =>
      (resolventWeight_ratio_atBot S (spectralWeights S J) k j hjk).comp tendsto_neg_atTop_atBot)
  simpa only [Function.comp_def,neg_neg,Equiv.refl_apply,resolventFlow,reconstructFiber,flowMeasure] using h.comp tendsto_neg_atBot_atTop

/-- The common energy of the two momentum-free endpoint schedules.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
def richardsonEnergy {N : ℕ} (S : Nodes N) : ℝ := ∑ i,((1-S.value i)⁻¹)^2

/-- Matrix convergence to any root ordering gives the literal inverse
energy. Positive root gaps justify continuity of the endpoint inverse.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem energy_limit_of_diagonal {N : ℕ} (S : Nodes N) {ι : Type*} {l : Filter ι}
    (J : ι → chebyshev2.Jacobi N) (ord : Fin N ≃ Fin N)
    (hJ : Tendsto (fun t => (J t).matrix) l (𝓝 (diagonal (fun i => S.value (ord i))))) :
    Tendsto (fun t => (J t).energy) l (𝓝 (richardsonEnergy S)) := by
  let D := diagonal (fun i => S.value (ord i))
  have hp : (1-D).PosDef := by
    rw [show (1 : Matrix (Fin N) (Fin N) ℝ)=diagonal (fun _ => 1) by rw [Matrix.diagonal_one],
      Matrix.diagonal_sub]
    exact Matrix.posDef_diagonal_iff.mpr (fun i => sub_pos.mpr (S.interval (ord i)).2)
  have hi : ContinuousAt (Inv.inv : Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (1-D) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hp.det_pos.ne'
  have hg := hi.tendsto.comp (tendsto_const_nhds.sub hJ)
  have hlim := tendsto_finsetSum Finset.univ (fun i _ =>
    (((continuous_apply i).tendsto _).comp (((continuous_apply i).tendsto _).comp hg)).pow 2)
  have he : (∑ i,((1-D)⁻¹ i i)^2)=richardsonEnergy S := by
    have hd : (1-D)⁻¹=diagonal (fun i => (1-S.value (ord i))⁻¹) := by
      apply Matrix.inv_eq_left_inv
      change diagonal (fun i => (1-S.value (ord i))⁻¹)*(1-diagonal (fun i => S.value (ord i)))=1
      rw [← Matrix.diagonal_one,Matrix.diagonal_sub,Matrix.diagonal_mul_diagonal]
      ext i j
      simp [Matrix.diagonal_apply,(sub_pos.mpr (S.interval (ord i)).2).ne']
    rw [hd]
    simpa only [richardsonEnergy,Matrix.diagonal_apply_eq] using
      Equiv.sum_comp ord (fun i => ((1-S.value i)⁻¹)^2)
  rw [he] at hlim
  exact hlim

/-- The positive-time limiting energy is exactly the root-gap square sum.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventFlow_energy_atTop {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    Tendsto (fun t : ℝ => (resolventFlow S J t).val.energy) atTop (𝓝 (richardsonEnergy S)) :=
  energy_limit_of_diagonal S (fun t => (resolventFlow S J t).val) Fin.revPerm (resolventFlow_atTop S J)

/-- The negative-time limit has the same exact energy, in the opposite ordering.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventFlow_energy_atBot {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    Tendsto (fun t : ℝ => (resolventFlow S J t).val.energy) atBot (𝓝 (richardsonEnergy S)) :=
  energy_limit_of_diagonal S (fun t => (resolventFlow S J t).val) (Equiv.refl _) (resolventFlow_atBot S J)

/-- For the actual Jacobi root lists, the endpoint schedules have a
strictly positive quartic energy constant given by the second Rayleigh sum.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem richardsonEnergy_jacobi_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun m : ℕ => richardsonEnergy (jacobi.Jacobi.nodes a b ha hb (m+1))/
      ((m+1:ℕ):ℝ)^4) atTop (𝓝 (1/(4*(a+1)^2*(a+2)))) := by
  have h := (jacobi.Jacobi.finiteLambda_square_sum_tendsto ha hb).comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext m
  rw [richardsonEnergy,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [jacobi.Jacobi.finiteLambda_node ha hb i]
  push_cast
  field_simp

end
end jacobi.Finite
