import jacobi.Finite.ExponentialTilt

/-!
Extreme-time concentration of the actual resolvent-flow probabilities.
Centering all exponential velocities at their unique extremum makes the
finite partition sum converge to its surviving positive initial weight.
Use: FlowSorting identifies which root reaches the first physical site
at each end of the flow; concentration alone is not full matrix sorting.
Article: jacobi, Proposition 5.5 and Section 5.6.
Article role: both sorted matrix limits, limiting Richardson energy and its quartic Jacobi
asymptotic.
-/
namespace jacobi.Finite
noncomputable section
open Real Filter
open scoped Topology BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- Subtracting a common exponential velocity does not change the
normalized probabilities. This is exact at every finite time.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem tiltWeight_center {n : ℕ} (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ)
    (t c : ℝ) (i : Fin (n+1)) :
    tiltWeight w v t i=
      w.val i*exp (t*(v i-c))/(∑ j,w.val j*exp (t*(v j-c))) := by
  have he (j : Fin (n+1)) : w.val j*exp (t*v j)=
      exp (t*c)*(w.val j*exp (t*(v j-c))) := by
    rw [mul_left_comm,← exp_add]
    congr 2
    ring
  unfold tiltWeight tiltNormalizer
  simp_rw [he]
  rw [← Finset.mul_sum,mul_div_mul_left _ _ (exp_ne_zero _)]

/-- At positive infinite time, a unique maximal velocity receives all
probability. Every other weight tends to zero, with no assumption about
the relative sizes of the positive initial weights.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem tiltWeight_max_limit {n : ℕ} (w : WeightSimplex (n+1))
    (v : Fin (n+1) → ℝ) (k : Fin (n+1)) (hk : ∀ j,j≠k → v j<v k)
    (i : Fin (n+1)) :
    Tendsto (fun t : ℝ => tiltWeight w v t i) atTop (𝓝 (if i=k then 1 else 0)) := by
  have he (j : Fin (n+1)) : Tendsto (fun t : ℝ => w.val j*exp (t*(v j-v k)))
      atTop (𝓝 (if j=k then w.val k else 0)) := by
    by_cases hj : j=k
    · subst j
      simp only [sub_self,mul_zero,exp_zero,mul_one,ite_true]
      exact tendsto_const_nhds
    · rw [ite_eq_right hj]
      have h := tendsto_exp_atBot.comp
        ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_const_of_neg
          (sub_neg.mpr (hk j hj)))
      simpa only [mul_zero,Function.comp_def,id_eq] using h.const_mul (w.val j)
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => he j)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hsum
  have h := (he i).div hsum (w.property.1 k).ne'
  simp_rw [tiltWeight_center w v _ (v k)]
  convert h using 1
  split_ifs <;> simp_all [(w.property.1 k).ne']

/-- Negative time is positive time with all velocities reversed.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem tiltWeight_neg_time {n : ℕ} (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ)
    (t : ℝ) (i : Fin (n+1)) :
    tiltWeight w v t i=tiltWeight w (fun j => -v j) (-t) i := by
  simp only [tiltWeight,tiltNormalizer,neg_mul_neg]

/-- At negative infinite time, the unique minimal velocity receives
all probability. This is the opposite endpoint of the same global flow.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem tiltWeight_min_limit {n : ℕ} (w : WeightSimplex (n+1))
    (v : Fin (n+1) → ℝ) (k : Fin (n+1)) (hk : ∀ j,j≠k → v k<v j)
    (i : Fin (n+1)) :
    Tendsto (fun t : ℝ => tiltWeight w v t i) atBot (𝓝 (if i=k then 1 else 0)) := by
  have h := (tiltWeight_max_limit w (fun j => -v j) k
    (fun j hj => neg_lt_neg (hk j hj)) i).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,← tiltWeight_neg_time] using h

/-- Descending roots give strictly increasing resolvent velocities.
Thus positive time selects the smallest root, and negative time the largest.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventVelocity_strictMono {n : ℕ} (S : Nodes (n+1)) :
    StrictMono (resolventVelocity S) := by
  intro i j hij
  have hn : 0<(n+1:ℝ)^2 := by positivity
  have hi : 0<1-S.value i := sub_pos.mpr (S.interval i).2
  have hj : 0<1-S.value j := sub_pos.mpr (S.interval j).2
  apply (div_lt_div_iff₀ (mul_pos hn hi) (mul_pos hn hj)).mpr
  have h := mul_pos hn (sub_pos.mpr (S.strictAnti hij))
  nlinarith

/-- Exact positive-time endpoint concentration for the actual resolvent
weights, in the original descending spectral index convention.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventWeights_atTop {n : ℕ} (S : Nodes (n+1)) (w : WeightSimplex (n+1))
    (i : Fin (n+1)) :
    Tendsto (fun t : ℝ => (resolventWeights S w t).val i) atTop
      (𝓝 (if i=Fin.last n then 1 else 0)) := by
  simp_rw [resolventWeights_eq_tilt]
  exact tiltWeight_max_limit w _ _ (fun j hj => resolventVelocity_strictMono S
    (lt_of_le_of_ne (Fin.le_last j) hj)) i

/-- Exact negative-time endpoint concentration for the actual resolvent
weights. The largest prescribed root is the surviving first-site mass.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem resolventWeights_atBot {n : ℕ} (S : Nodes (n+1)) (w : WeightSimplex (n+1))
    (i : Fin (n+1)) :
    Tendsto (fun t : ℝ => (resolventWeights S w t).val i) atBot
      (𝓝 (if i=0 then 1 else 0)) := by
  simp_rw [resolventWeights_eq_tilt]
  exact tiltWeight_min_limit w _ _ (fun j hj => resolventVelocity_strictMono S
    (Fin.pos_iff_ne_zero.mpr hj)) i

end
end jacobi.Finite
