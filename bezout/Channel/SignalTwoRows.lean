import bezout.Channel.SignalBounds

/-!
Article: bezout, Appendix D, endpoint Gram and finite-bulk transfer estimates.
Use: two equal-energy endpoint profiles have exact squared channel norm E+|c|,
where c is their temporal inner product. Equal mode masses give w(E+|c|).
Proof: temporal Cauchy--Schwarz gives the upper bound through the dual combination
alpha*u+beta*v; the normalized profile u+sign(c)*v attains the bound.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ}

/-- Temporal Euclidean inner product of two scalar insertion profiles. -/
def temporalDot (u v : Fin N → ℝ) : ℝ := ∑ s, u s*v s

/-- The temporal inner product is symmetric. -/
theorem temporalDot_comm (u v : Fin N → ℝ) : temporalDot u v=temporalDot v u := by
  simp only [temporalDot, mul_comm]

/-- Temporal squared norm as a sum of squares. -/
theorem temporalDot_self (u : Fin N → ℝ) : temporalDot u u=∑ s, u s^2 := by
  simp only [temporalDot, pow_two]

/-- Linearity in the right temporal profile. -/
theorem temporalDot_linear_right (u v w : Fin N → ℝ) (a b : ℝ) :
    temporalDot u (fun s => a*v s+b*w s)=a*temporalDot u v+b*temporalDot u w := by
  simp only [temporalDot, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Linearity in the left temporal profile. -/
theorem temporalDot_linear_left (u v w : Fin N → ℝ) (a b : ℝ) :
    temporalDot (fun s => a*u s+b*v s) w=a*temporalDot u w+b*temporalDot v w := by
  rw [temporalDot_comm, temporalDot_linear_right, temporalDot_comm w u, temporalDot_comm w v]

/-- Exact squared norm of a temporal linear combination. -/
theorem temporalDot_linear_self (u v : Fin N → ℝ) (a b : ℝ) :
    temporalDot (fun s => a*u s+b*v s) (fun s => a*u s+b*v s)=
      a^2*temporalDot u u+b^2*temporalDot v v+2*a*b*temporalDot u v := by
  rw [temporalDot_linear_left, temporalDot_linear_right, temporalDot_linear_right,
    temporalDot_comm v u]
  ring

/-- Temporal inner products respect independent scalar rescalings. -/
theorem temporalDot_scale (u v : Fin N → ℝ) (a b : ℝ) :
    temporalDot (fun s => a*u s) (fun s => b*v s)=a*b*temporalDot u v := by
  simp only [temporalDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Division by a common scalar commutes with a temporal inner product. -/
theorem temporalDot_div_right (u v : Fin N → ℝ) (a : ℝ) :
    temporalDot u (fun s => v s/a)=temporalDot u v/a := by
  simp only [temporalDot, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Temporal Cauchy--Schwarz in squared algebraic form. -/
theorem temporalDot_sq_le (u v : Fin N → ℝ) :
    temporalDot u v^2≤temporalDot u u*temporalDot v v := by
  simpa only [temporalDot, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

/-- The literal two-endpoint channel matrix. -/
def twoRowMatrix (u v : Fin N → ℝ) : Matrix (Fin 2) (Fin N) ℝ := ![u,v]

/-- Exact output energy of the actual two-row channel action. -/
theorem twoRow_action_sq (u v : Fin N → ℝ) (e : EuclideanSpace ℝ (Fin N)) :
    ‖rectangularOperator (twoRowMatrix u v) e‖^2=
      temporalDot u e.ofLp^2+temporalDot v e.ofLp^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  change (∑ s, u s*e s)^2+(∑ s, v s*e s)^2=_
  rfl

/-- Equal-energy rows have the sharp upper coefficient E+|c|. -/
theorem twoRow_action_sq_le (u v : Fin N → ℝ) (R : ℝ)
    (hu : temporalDot u u=R) (hv : temporalDot v v=R)
    (e : EuclideanSpace ℝ (Fin N)) :
    ‖rectangularOperator (twoRowMatrix u v) e‖^2≤(R+|temporalDot u v|)*‖e‖^2 := by
  let a := temporalDot u e.ofLp
  let b := temporalDot v e.ofLp
  let A := a^2+b^2
  let c := temporalDot u v
  let C := R+|c|
  let w : Fin N → ℝ := fun s => a*u s+b*v s
  have hR : 0≤R := by rw [← hu, temporalDot_self]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0≤C := add_nonneg hR (abs_nonneg _)
  have hA : 0≤A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hew : temporalDot e.ofLp w=A := by
    rw [temporalDot_linear_right, temporalDot_comm e.ofLp u, temporalDot_comm e.ofLp v]
    dsimp only [a,b,A]
    ring
  have hww : temporalDot w w=R*A+2*c*a*b := by
    rw [temporalDot_linear_self, hu, hv]
    dsimp only [A,c]
    ring
  have hcross : 2*c*a*b≤|c| *A := by
    by_cases hc : 0≤c
    · rw [abs_of_nonneg hc]
      have hp := mul_nonneg hc (sq_nonneg (a-b))
      dsimp only [A]
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hc)]
      have hp := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hc)) (sq_nonneg (a+b))
      dsimp only [A]
      nlinarith
  have hw : temporalDot w w≤C*A := by
    rw [hww]
    calc
      _ ≤ R*A+|c| *A := add_le_add (le_refl _) hcross
      _ = C*A := by dsimp only [C]; ring
  have hcs := temporalDot_sq_le e.ofLp w
  rw [hew] at hcs
  have hee : temporalDot e.ofLp e.ofLp=‖e‖^2 := by
    rw [temporalDot_self, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hee] at hcs
  have hprod : A*A≤(C*‖e‖^2)*A := by
    calc
      _ = A^2 := by ring
      _ ≤ ‖e‖^2*temporalDot w w := hcs
      _ ≤ ‖e‖^2*(C*A) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = _ := by ring
  rw [twoRow_action_sq]
  change A≤C*‖e‖^2
  by_cases hz : A=0
  · rw [hz]; exact mul_nonneg hC (sq_nonneg _)
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hA (Ne.symm hz))).mp hprod

/-- Exact two-endpoint Gram formula for the actual squared operator norm. -/
theorem twoRow_norm_sq (u v : Fin N → ℝ) (R : ℝ)
    (hu : temporalDot u u=R) (hv : temporalDot v v=R) :
    rectangularNorm (twoRowMatrix u v)^2=R+|temporalDot u v| := by
  let c := temporalDot u v
  let C := R+|c|
  have hR : 0≤R := by rw [← hu, temporalDot_self]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0≤C := add_nonneg hR (abs_nonneg _)
  have hup : rectangularNorm (twoRowMatrix u v)^2≤C :=
    rectangularNorm_sq_le _ hC (twoRow_action_sq_le u v R hu hv)
  apply le_antisymm hup
  by_cases hz : C=0
  · rw [hz]; exact sq_nonneg _
  · have hCp : 0<C := lt_of_le_of_ne hC (Ne.symm hz)
    let z : ℝ := if 0≤c then 1 else -1
    have hz2 : z^2=1 := by unfold z; split_ifs <;> norm_num
    have hzc : z*c=|c| := by unfold z; split_ifs with hc <;> simp [abs_of_nonneg, abs_of_neg, hc, lt_of_not_ge]
    have hcz : c=z*|c| := by rw [← hzc, ← mul_assoc, ← pow_two, hz2, one_mul]
    let w : Fin N → ℝ := fun s => 1*u s+z*v s
    have hww : temporalDot w w=2*C := by
      have he := temporalDot_linear_self u v 1 z
      simp only [one_mul] at he
      change temporalDot (fun s => 1*u s+z*v s) (fun s => 1*u s+z*v s)=2*C
      rw [temporalDot_linear_self, hu, hv, hz2]
      dsimp only [C]
      nlinarith [hzc]
    have huw : temporalDot u w=C := by
      change temporalDot u (fun s => 1*u s+z*v s)=C
      rw [temporalDot_linear_right, hu]
      dsimp only [C,c] at *
      nlinarith [hzc]
    have hvw : temporalDot v w=z*C := by
      change temporalDot v (fun s => 1*u s+z*v s)=z*C
      rw [temporalDot_linear_right, hv, temporalDot_comm v u]
      dsimp only [C,c] at *
      nlinarith [hcz]
    let q := Real.sqrt (2*C)
    have hq : 0<q := Real.sqrt_pos.mpr (by positivity)
    have hq2 : q^2=2*C := Real.sq_sqrt (by positivity)
    let e : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun s => w s/q)
    have hee : ‖e‖^2=1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [e, Real.norm_eq_abs, sq_abs, div_pow, ← Finset.sum_div]
      rw [← temporalDot_self, hww, hq2]
      field_simp
    have he : ‖e‖=1 := by nlinarith [norm_nonneg e]
    have hue : temporalDot u e.ofLp=C/q := by change temporalDot u (fun s => w s/q)=_; rw [temporalDot_div_right, huw]
    have hve : temporalDot v e.ofLp=z*C/q := by change temporalDot v (fun s => w s/q)=_; rw [temporalDot_div_right, hvw]
    have hout : ‖rectangularOperator (twoRowMatrix u v) e‖^2=C := by
      rw [twoRow_action_sq, hue, hve, div_pow, div_pow, mul_pow, hz2, one_mul]
      field_simp
      nlinarith [hq2]
    have hop := (rectangularOperator (twoRowMatrix u v)).le_opNorm e
    rw [he, mul_one] at hop
    have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hop
    rw [hout] at hsq
    exact hsq

/-- Equal endpoint mode masses multiply the exact two-row Gram coefficient by w. -/
theorem twoRow_weighted_norm_sq (u v : Fin N → ℝ) (R w a b : ℝ)
    (hu : temporalDot u u=R) (hv : temporalDot v v=R) (ha : a^2=w) (hb : b^2=w) :
    rectangularNorm (twoRowMatrix (fun s => a*u s) (fun s => b*v s))^2=w*(R+|temporalDot u v|) := by
  have hw : 0≤w := by rw [← ha]; exact sq_nonneg _
  have hab : |a*b|=w := by
    apply (sq_eq_sq₀ (abs_nonneg _) hw).mp
    rw [sq_abs, mul_pow, ha, hb]
    ring
  rw [twoRow_norm_sq _ _ (w*R) (by rw [temporalDot_scale, ← pow_two, ha, hu])
    (by rw [temporalDot_scale, ← pow_two, hb, hv]), temporalDot_scale, abs_mul, hab]
  ring

end
end bezout.Channel
