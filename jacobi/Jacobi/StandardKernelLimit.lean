import jacobi.Jacobi.StandardCoefficientLimit
import jacobi.Analysis.PowerTail

/-!
Moving-mesh limits of the genuine standard Jacobi Green tails.
The endpoint norms and conductances are the proved original ones. Their
positive power laws feed the exact finite tail formula, including the
zero extension at the final vertex required by the floor convention.
Use: StandardJacobi turns these limits into uniform kernel convergence,
energy convergence and the actual initial derivative limit of the flow.
Article: jacobi, Theorem 5.4, Equation (5.9).
Article role: the moving-mesh conductance-tail limit of actual Green entries.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory jacobi.Analysis
set_option backward.isDefEq.respectTransparency false
open scoped Topology

/-- The exact finite Green formula on natural indices, extended by zero
beyond the final vertex because its conductance tail is empty there.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
def standardGreenTail (a b : ℝ) (N i j : ℕ) : ℝ :=
  standardEndpoint a b i*standardEndpoint a b j*
    ∑ l∈Finset.range N,if max i j≤l then (standardConductance a b l)⁻¹ else 0

/-- The true one-sided limit kernel in its nonsingular tail-integral
form on positive arguments. This representation also covers a=0.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
def standardLimitKernel (a s t : ℝ) : ℝ :=
  2*sqrt (s^(2*a+1)*t^(2*a+1))*∫ v in max s t..1,1/v^(2*a+1)

/-- The extended formula agrees with every actual upper-triangular
entry of the standard Green matrix. The lower triangle follows by symmetry.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardGreenTail_entry_of_le {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {N : ℕ} (i j : Fin N) (hij : i≤j) :
    standardGreenTail a b N i j=(standardChain a b ha hb N).green i j := by
  rw [standard_green_entry ha hb i j hij]
  unfold standardGreenTail
  rw [max_eq_right (show i.val≤j.val from hij)]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun l : ℕ =>
    if j.val≤l then (standardConductance a b l)⁻¹ else 0) N).symm

/-- All finite natural-index tails are nonnegative, including their
zero extension at and beyond the terminal mesh point.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardGreenTail_nonneg {a b : ℝ} (ha : -1<a) (hb : -1<b) (N i j : ℕ) :
    0≤standardGreenTail a b N i j := by
  apply mul_nonneg (mul_nonneg (standardEndpoint_pos ha hb i).le (standardEndpoint_pos ha hb j).le)
  apply Finset.sum_nonneg
  intro l _
  split_ifs
  · exact (inv_pos.mpr (standardConductance_pos ha hb l)).le
  · exact le_refl 0

/-- The true endpoint product has its normalized moving-mesh limit.
Taking positive square roots preserves the actual orthonormal signs.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardEndpoint_product_mesh_limit {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (n i j : ℕ → ℕ) {s t : ℝ} (hs : 0<s) (ht : 0<t) (hn : Tendsto n atTop atTop)
    (hi : Tendsto (fun k => (i k:ℝ)/(n k:ℝ)) atTop (𝓝 s))
    (hj : Tendsto (fun k => (j k:ℝ)/(n k:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun k => standardEndpoint a b (i k)*standardEndpoint a b (j k)/(n k:ℝ)^(2*a+1))
      atTop (𝓝 (sqrt ((standardEndpointConstant a b*s^(2*a+1))*
        (standardEndpointConstant a b*t^(2*a+1))))) := by
  have hU := standardEndpointSquare_power_limit ha hb
  have h := ((power_mesh_limit _ hU hs hn hi).mul (power_mesh_limit _ hU ht hn hj)).sqrt
  apply h.congr'
  filter_upwards [hn.eventually_gt_atTop 0] with k hnk
  have hP : 0<(n k:ℝ)^(2*a+1) := rpow_pos_of_pos (Nat.cast_pos.mpr hnk) _
  rw [div_mul_div_comm,sqrt_div (mul_nonneg (standardEndpointSquare_pos ha hb (i k)).le
    (standardEndpointSquare_pos ha hb (j k)).le),
    sqrt_mul (standardEndpointSquare_pos ha hb (i k)).le,sqrt_mul_self hP.le]
  rfl

/-- The complete inverse-conductance tail has its genuine moving
physical integral limit. No uniform tail asymptotic is left as an input.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardConductance_tail_limit {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (n j : ℕ → ℕ) {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hn : Tendsto n atTop atTop)
    (hj : Tendsto (fun k => (j k:ℝ)/(n k:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun k => (∑ l∈Finset.range (n k),if j k≤l then
      (n k:ℝ)^(2*a+1)/standardConductance a b l else 0)/(n k:ℝ)) atTop
      (𝓝 (∫ v in t..1,1/((standardEndpointConstant a b/2)*v^(2*a+1)))) :=
  reciprocal_power_tail_limit _ (div_pos (standardEndpointConstant_pos ha hb) (by norm_num))
    (standardConductance_power_limit ha hb) n j ht hn hj

/-- The genuine extended standard Green kernel converges along every
positive moving pair of physical indices, including the terminal point
one. The common probability-weight amplitude cancels exactly, proving
that the limiting geometry is independent of b.
Article: jacobi, Theorem 5.4, Equation (5.9).
-/
theorem standardGreenTail_mesh_limit {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (n i j : ℕ → ℕ) {s t : ℝ} (hs : s∈Ioc (0:ℝ) 1) (ht : t∈Ioc (0:ℝ) 1)
    (hn : Tendsto n atTop atTop)
    (hi : Tendsto (fun k => (i k:ℝ)/(n k:ℝ)) atTop (𝓝 s))
    (hj : Tendsto (fun k => (j k:ℝ)/(n k:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun k => standardGreenTail a b (n k) (i k) (j k)/(n k:ℝ))
      atTop (𝓝 (standardLimitKernel a s t)) := by
  let C := standardEndpointConstant a b
  have hC : 0<C := standardEndpointConstant_pos ha hb
  have hmax : Tendsto (fun k => ((max (i k) (j k):ℕ):ℝ)/(n k:ℝ)) atTop (𝓝 (max s t)) := by
    convert hi.max hj using 1
    funext k
    rw [Nat.cast_max,← max_div_div_right (Nat.cast_nonneg (n k))]
  have h := (standardEndpoint_product_mesh_limit ha hb n i j hs.1 ht.1 hn hi hj).mul
    (standardConductance_tail_limit ha hb n (fun k => max (i k) (j k))
      ⟨hs.1.trans_le (le_max_left _ _),max_le hs.2 ht.2⟩ hn hmax)
  have hroot : sqrt ((C*s^(2*a+1))*(C*t^(2*a+1)))=
      C*sqrt (s^(2*a+1)*t^(2*a+1)) := by
    rw [show (C*s^(2*a+1))*(C*t^(2*a+1))=C^2*(s^(2*a+1)*t^(2*a+1)) by ring,
      sqrt_mul (sq_nonneg C),sqrt_sq hC.le]
  have hfun : (fun v : ℝ => 1/((C/2)*v^(2*a+1)))=
      fun v => (2/C)*(1/v^(2*a+1)) := by
    funext v
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  change Tendsto _ atTop (𝓝 (sqrt ((C*s^(2*a+1))*(C*t^(2*a+1)))*
    ∫ v in max s t..1,1/((C/2)*v^(2*a+1)))) at h
  rw [hroot,hfun,intervalIntegral.integral_const_mul] at h
  have hconst : (C*sqrt (s^(2*a+1)*t^(2*a+1)))*
      ((2/C)*(∫ v in max s t..1,1/v^(2*a+1)))=standardLimitKernel a s t := by
    unfold standardLimitKernel
    field_simp [hC.ne']
  rw [hconst] at h
  apply h.congr'
  filter_upwards [hn.eventually_gt_atTop 0] with k hnk
  have hP : (n k:ℝ)^(2*a+1)≠0 := (rpow_pos_of_pos (Nat.cast_pos.mpr hnk) _).ne'
  have hsum : (∑ l∈Finset.range (n k),if max (i k) (j k)≤l then
      (n k:ℝ)^(2*a+1)/standardConductance a b l else 0)=
        (n k:ℝ)^(2*a+1)*∑ l∈Finset.range (n k),if max (i k) (j k)≤l then
          (standardConductance a b l)⁻¹ else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp only [mul_zero,div_eq_mul_inv]
  rw [hsum]
  unfold standardGreenTail
  field_simp [hP]

end
end jacobi.Jacobi
