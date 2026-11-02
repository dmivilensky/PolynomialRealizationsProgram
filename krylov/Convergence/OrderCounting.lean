import krylov.Convergence.Order
import krylov.Convergence.CharacteristicComparison

/-!
Article: main_krylov, Table s7-orders and its gradient-count convention.
Use: convert an actual cycle R-order into its per-iteration or per-gradient
order by an exact positive integral clock. The clocked barrier bounds every
intermediate error whenever the genuine finite-cycle localization supplies
its usual constant-factor comparison with the current cycle's initial error.
Source: integer division and monotonicity of geometric real powers.
-/
namespace krylov.Convergence
noncomputable section

/-- Exact integral clocks dilute an R-order by the true cost-th root.
Article: main_krylov, Table s7-orders. -/
theorem HasROrder.clock {e : ℕ → ℝ} {d : ℝ} (h : HasROrder e d)
    (hd : 1<d) (cost : ℕ) (hcost : 0<cost) :
    HasROrder (fun k=>e (k/cost)) (d^(1/(cost:ℝ))) := by
  obtain ⟨C,q,hC,hq,hq₁,hbound⟩ := h
  let τ := d^(1/(cost:ℝ))
  have hd₀ : 0<d := zero_lt_one.trans hd
  have hτ : 1<τ := Real.one_lt_rpow hd (by positivity)
  have hτ₀ : 0<τ := zero_lt_one.trans hτ
  have hpow : τ^cost=d := rpow_inverse_nat_pow hd₀ hcost
  refine ⟨C,q^(1/d),hC,Real.rpow_pos_of_pos hq _,Real.rpow_lt_one hq.le hq₁ (by positivity),?_⟩
  intro k
  have hexp : τ^k≤d*d^(k/cost) := by
    have hidx : k=(k/cost)*cost+k%cost := by simpa only [Nat.mul_comm] using (Nat.div_add_mod k cost).symm
    calc
      τ^k=τ^((k/cost)*cost)*τ^(k%cost) := by rw [←pow_add,←hidx]
      _ = d^(k/cost)*τ^(k%cost) := by rw [Nat.mul_comm _ cost,pow_mul,hpow]
      _ ≤ d^(k/cost)*τ^cost := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hτ.le (Nat.mod_lt k hcost).le) (pow_nonneg hd₀.le _)
      _ = _ := by rw [hpow,mul_comm]
  have he : (1/d)*τ^k≤d^(k/cost) := by
    have hh : τ^k/d≤d^(k/cost) := (div_le_iff₀ hd₀).mpr (by simpa only [mul_comm] using hexp)
    simpa only [one_div,div_eq_inv_mul,mul_one] using hh
  have hgeom : q^(d^(k/cost))≤(q^(1/d))^(τ^k) := by
    rw [←Real.rpow_mul hq.le]
    exact Real.rpow_le_rpow_of_exponent_ge hq hq₁.le he
  exact (hbound (k/cost)).trans (mul_le_mul_of_nonneg_left hgeom hC.le)

/-- A real intermediate-iterate bound transfers the exact cycle clock to
the same printed per-cost R-order. Article: main_krylov, Table s7-orders. -/
theorem HasROrder.clock_mono {e f : ℕ → ℝ} {d : ℝ} (h : HasROrder e d)
    (hd : 1<d) (cost : ℕ) (hcost : 0<cost) {A : ℝ} (hA : 0<A)
    (hintermediate : ∀ k,f k≤A*e (k/cost)) :
    HasROrder f (d^(1/(cost:ℝ))) :=
  (h.clock hd cost hcost).mono hA hintermediate

end
end krylov.Convergence
