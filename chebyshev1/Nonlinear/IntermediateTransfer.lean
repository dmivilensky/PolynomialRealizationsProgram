import chebyshev1.Nonlinear.Methods

/-! Intermediate transfers for endpoint-maximizing Jacobi chains. These estimates
apply to the fixed full-horizon chain, including its proper leading blocks. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
variable (J : JacobiData) (I : SpectralInterval)

theorem endpointMax_restrict {N n : ℕ} (hm : J.EndpointMax N) (hn : n ≤ N) :
    J.EndpointMax n := by
  intro a k hak
  exact hm a k (hak.trans hn)

theorem endpointWeight_nonneg {N : ℕ} (hm : J.EndpointMax N)
    (times : Finset ℕ) (ht : times ⊆ Finset.range N) :
    0 ≤ J.endpointWeight N times := by
  rw [J.endpointWeight_eq_partitionWeight hm le_rfl times ht]
  exact J.blockWord_bound_nonneg _ _

theorem leading_eval_mono {N : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (J.leading N).eval x ≤ (J.leading N).eval y := by
  have he (z : ℝ) : (J.leading N).eval z =
      ∑ times ∈ (Finset.range N).powerset,
        J.endpointWeight N times * (z-1)^times.card := by
    have hh := congrArg (fun p : ℝ[X] => p.eval (z-1)) (J.taylor_leading_partition I h)
    simpa only [taylor_eval, sub_add_cancel, eval_finsetSum, eval_mul, eval_C,
      eval_pow, eval_X] using hh
  rw [he x, he y]
  apply Finset.sum_le_sum
  intro times ht
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0 ≤ x-1) (by linarith : x-1 ≤ y-1) _)
    (J.endpointWeight_nonneg hm times (Finset.mem_powerset.mp ht))

theorem opNorm_transfer_le_leading {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (Hs s-H) ≤ delta) :
    opNorm ((J.realization I).operatorTransfer N Hs) ≤
      (J.leading N).eval (1+2*delta/I.delta) / J.den I N := by
  let E := fun s => Hs s-H
  have he : (fun s => H+E s) = Hs := by funext s; dsimp [E]; abel
  have hsum : (J.leading N).eval (1+2*delta/I.delta) / J.den I N =
      ∑ times ∈ (Finset.range N).powerset,
        ((2/I.delta)^times.card / J.den I N) *
          (delta^times.card * J.partitionWeight N times) := by
    have hp := congrArg (fun p : ℝ[X] => p.eval (2*delta/I.delta))
      (J.taylor_leading_partition I h)
    simp only [taylor_eval, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at hp
    rw [add_comm] at hp
    rw [hp, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro times ht
    rw [J.endpointWeight_eq_partitionWeight hm le_rfl times (Finset.mem_powerset.mp ht)]
    rw [show 2*delta/I.delta = (2/I.delta)*delta by ring, mul_pow]
    ring
  rw [← he, J.finiteDrift_words I h]
  calc
    _ ≤ ∑ times ∈ (Finset.range N).powerset,
        opNorm (((-(2/I.delta))^times.card/J.den I N) • J.operatorWord I H E N times) :=
      norm_sum_le _ _
    _ ≤ ∑ times ∈ (Finset.range N).powerset,
        ((2/I.delta)^times.card / J.den I N) *
          (delta^times.card * J.partitionWeight N times) := by
      apply Finset.sum_le_sum
      intro times ht
      rw [opNorm_smul, abs_div, abs_pow, abs_neg,
        abs_of_pos (div_pos (by norm_num) I.delta_pos), abs_of_pos (h N le_rfl)]
      exact mul_le_mul_of_nonneg_left
        (J.opNorm_operatorWord_le I N H hH hspec E delta hd hE N le_rfl times
          (Finset.mem_powerset.mp ht))
        (div_nonneg (pow_nonneg (div_nonneg (by norm_num) I.delta_pos.le) _) (h N le_rfl).le)
    _ = _ := hsum.symm

theorem opNorm_transfer_le_one {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hdmu : delta ≤ I.mu)
    (hE : ∀ s < N, opNorm (Hs s-H) ≤ delta) :
    opNorm ((J.realization I).operatorTransfer N Hs) ≤ 1 := by
  refine (J.opNorm_transfer_le_leading I h hm H hH hspec Hs delta hd hE).trans ?_
  apply (div_le_one (h N le_rfl)).mpr
  change (J.leading N).eval (1+2*delta/I.delta) ≤ (J.leading N).eval I.eta
  apply J.leading_eval_mono I h hm (le_add_of_nonneg_right
    (div_nonneg (by positivity) I.delta_pos.le))
  rw [I.eta_eq_one_add]
  simpa only [add_comm] using add_le_add_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdmu (by norm_num : (0:ℝ) ≤ 2)) I.delta_pos.le) 1

end
end chebyshev1.JacobiData

namespace chebyshev1.Nonlinear
noncomputable section

theorem MethodFamily.admissible (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) : (family.data N).Admissible I N := by
  cases family with
  | «prefix» => exact Prefix.jacobi_admissible I N
  | sine => exact SineJacobi.admissible I N hN

theorem MethodFamily.endpointMax (family : MethodFamily) {N : ℕ} (hN : 0 < N) :
    (family.data N).EndpointMax N := by
  cases family with
  | «prefix» => exact Prefix.jacobi_endpointMax N
  | sine => exact SineJacobi.endpointMax N hN

theorem MethodFamily.intermediate_transfer_le_one (family : MethodFamily)
    (I : SpectralInterval) {N : ℕ} (hN : 0 < N) {n : ℕ} (hn : n ≤ N)
    {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hdmu : delta ≤ I.mu)
    (hE : ∀ s < n, opNorm (Hs s-H) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer n Hs) ≤ 1 :=
  (family.data N).opNorm_transfer_le_one I
    (fun k hk => family.admissible I hN k (hk.trans hn))
    ((family.data N).endpointMax_restrict (family.endpointMax hN) hn)
    H hH hspec Hs delta hd hdmu hE

end
end chebyshev1.Nonlinear
