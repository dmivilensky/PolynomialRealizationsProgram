import bezout.Comparisons.Competitors.Propagation

/-!
Article: bezout, physical competitor response formulas and variance predictions.
Use: an actual momentum execution is its nominal trajectory plus the exact
superposition of its physical unit-answer-error trajectories.
Proof: linear forcing decomposes in the finite time basis, and the same actual
matrix recursion preserves sums and scalar multiples of its physical inputs.
-/

namespace bezout.Comparisons.Competitors.Momentum
noncomputable section
open scoped BigOperators Matrix

/-- The complete physical forcing is the finite sum of its scaled unit impulses. -/
theorem scalarForcing_superposition (data : Momentum) (N : ℕ) (noise : Fin N → ℝ) :
    data.scalarForcing N noise = fun j => ∑ s : Fin N,
      noise s • data.scalarForcing N (fun t => if t=s then 1 else 0) j := by
  funext j
  by_cases hj : j<N
  · ext i
    fin_cases i <;>
      simp [scalarForcing,hj,Finset.sum_apply,smul_eq_mul,
        mul_ite,mul_comm]
  · simp [scalarForcing,hj]

/-- The actual scalar state superposes its nominal input and every physical error. -/
theorem scalarState_superposition (data : Momentum) (N : ℕ) (lam initial : ℝ)
    (noise : Fin N → ℝ) (k : ℕ) (hk : k≤N) :
    data.scalarState N lam initial noise k =
      initial • data.scalarState N lam 1 (fun _ => 0) k +
        ∑ s : Fin N, noise s • data.scalarState N lam 0 (fun t => if t=s then 1 else 0) k := by
  rw [data.scalarState_eq_linearRun N lam initial noise k hk]
  simp_rw [data.scalarState_eq_linearRun N lam 1 _ k hk,
    data.scalarState_eq_linearRun N lam 0 _ k hk]
  have hvec0 : ![(0:ℝ),0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hvec0]
  have hz : data.scalarForcing N (fun _ => 0) = fun _ => 0 := by
    funext j
    simp [scalarForcing]
  rw [hz]
  have hinit : ![initial,initial] = initial • ![(1:ℝ),1] + (0 : Fin 2 → ℝ) := by
    ext i; fin_cases i <;> simp
  rw [hinit,data.scalarForcing_superposition N noise]
  have hf : (fun j => ∑ s : Fin N,
      noise s • data.scalarForcing N (fun t => if t=s then 1 else 0) j) =
      (fun j => (0 : Fin 2 → ℝ)+∑ s : Fin N,
        noise s • data.scalarForcing N (fun t => if t=s then 1 else 0) j) := by simp
  rw [hf,linearRun_add,linearRun_forcing_sum]
  have hnom := linearRun_smul (fun j => data.matrix j lam) (fun _ => (0 : Fin 2 → ℝ))
    ![(1:ℝ),1] initial k
  simp only [smul_zero] at hnom
  rw [hnom]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have hp := linearRun_smul (fun j => data.matrix j lam)
    (data.scalarForcing N (fun t => if t=s then 1 else 0)) (0 : Fin 2 → ℝ) (noise s) k
  simpa only [smul_zero] using hp

end
end bezout.Comparisons.Competitors.Momentum
