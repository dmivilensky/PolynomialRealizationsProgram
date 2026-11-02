import krylov.Convergence.SS1OldestAsymptotic

/-!
Article: main_krylov, thm:Ip, exact oldest-pair coefficient for SS1.
Use: state the sharp bound with an arbitrary vanishing coefficient loss;
the actual distance Δ_k is retained, rather than replaced by its lower
conditioning bound. This is the quantified meaning of the printed 1+o(1).
Source: the proved genuine oldest-pair asymptotics and elementary scalar
little-o calculus. Zero Lipschitz constants are included.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Actual oldest distances of unit-column windows never exceed one. -/
theorem oldest_distance_unit_upper (V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hcol : ‖euclideanColumn V 0‖=1) :
    Metric.infDist (euclideanColumn V 0) (newerColumnSpan V:Set _)≤1 := by
  have hh := Metric.infDist_le_dist_of_mem (x:=euclideanColumn V 0)
    (show (0:EuclideanSpace ℝ (Fin (n+1)))∈(newerColumnSpan V:Set _) from Submodule.zero_mem _)
  simpa only [dist_zero_right,hcol] using hh

/-- An actual oldest-diagonal asymptotic estimate has precisely its sharp
distance coefficient. All vanishing remainders are discharged here. -/
theorem oldest_asymptotic_sharp {α : Type*} {l : Filter α}
    (q a v e D r : α → ℝ) {L : ℝ} (hq : ∀ z,0≤q z) (hv : ∀ z,0≤v z)
    (ha : a =o[l] q) (hr : r =o[l] q)
    (hD : ∀ᶠ z in l,0<D z ∧D z≤1)
    (hb : ∀ᶠ z in l,e z≤(L/2*(q z+a z)/(D z)^2+r z)*v z) :
    ∀ η : ℝ,0<η →∀ᶠ z in l,e z≤((L/2+η)/(D z)^2)*q z*v z := by
  intro η hη
  have hla : (fun z=>L/2*a z) =o[l] q := by
    simpa only [Pi.smul_apply,smul_eq_mul] using! ha.const_smul_left (L/2)
  filter_upwards [hD,hb,hla.def (half_pos hη),hr.def (half_pos hη)] with z hDz hbz haz hrz
  have hqz : ‖q z‖=q z := Real.norm_of_nonneg (hq z)
  rw [hqz] at haz hrz
  have hsquare : (D z)^2≤1 := by nlinarith only [hDz.1,hDz.2]
  have hrD : r z*(D z)^2≤η/2*q z := by
    have hh := mul_le_mul_of_nonneg_right (le_abs_self (r z)) (sq_nonneg (D z))
    have hh' := mul_le_mul_of_nonneg_left hsquare (abs_nonneg (r z))
    simp only [mul_one] at hh'
    exact (hh.trans hh').trans hrz
  have hlin : L/2*a z≤η/2*q z := (le_abs_self _).trans haz
  apply hbz.trans
  apply mul_le_mul_of_nonneg_right _ (hv z)
  conv_rhs => rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hDz.1)).mpr
  have he : (L/2*(q z+a z)/(D z)^2+r z)*(D z)^2=
      L/2*(q z+a z)+r z*(D z)^2 := by
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hDz.1.ne')]
  rw [he]
  nlinarith only [hrD,hlin]

/-- Exact source-level SS1 oldest-pair constant. Uniform normalized
independence is the only geometry hypothesis; the real model inverse,
superlinearity, and separation of all newer terms are proved internally. -/
theorem ss1Sequence_sharp_oldest_constant
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0)) {σ : ℝ} (hσ : 0<σ)
    (hind : ∀ᶠ k in atTop,IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k)))) :
    ∀ η : ℝ,0<η →∀ᶠ k in atTop,
      ‖ss1Sequence G seed (k+n+2)‖≤
        (((L:ℝ)/2+η)/(slidingOldestDistance (ss1Sequence G seed) k)^2)*
          ‖ss1Sequence G seed k‖*‖ss1Sequence G seed (k+n+1)‖ := by
  let x := ss1Sequence G seed
  obtain ⟨r,hr,hbound⟩ := ss1Sequence_oldest_asymptotic G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
  have hsuper := ss1Sequence_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
  have hD : ∀ᶠ k in atTop,0<slidingOldestDistance x k ∧slidingOldestDistance x k≤1 := by
    filter_upwards [hind] with k hk
    let V := windowMatrix (unitWindow (windowStep (n:=n+1) x k))
    have hs (i : Fin (n+1)) : windowStep (n:=n+1) x k i≠0 := by
      intro hz
      have hh := windowMatrix_step_ne_zero (unitWindow (windowStep x k)) hk.1 i
      apply hh
      simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
    have hcol : ‖euclideanColumn V 0‖=1 := unitWindow_norm (windowStep x k) hs 0
    exact ⟨hσ.trans_le (hk.2.trans (oldest_distance_leastGain V hk.1)),
      oldest_distance_unit_upper V hcol⟩
  exact oldest_asymptotic_sharp (fun k=>‖x k‖) (fun k=>‖x (k+1)‖)
    (fun k=>‖x (k+n+1)‖) (fun k=>‖x (k+n+2)‖) (slidingOldestDistance x) r
    (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
    (by simpa only [Nat.add_zero] using superlinear_window_tail x hsuper 0) hr hD hbound

end
end krylov.Convergence
