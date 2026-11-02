import jacobi.Reference.PositiveGammaRatio

/-!
Power asymptotics along moving mesh indices.
A positive limiting index ratio forces both indices to infinity, and
the exact positive real-power quotient transfers the original asymptotic.
Use: the standard Jacobi endpoint and inverse conductance mesh limits
reuse this statement with their already proved genuine power constants.
Article: jacobi, Theorem 5.4.
Article role: positive power normalization and Riemann sums for the conductance tails.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
namespace jacobi.Analysis
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Positive physical mesh position forces the moving numerator index
to infinity along any filter, rather than assuming a fixed-index tail.
Article: jacobi, Theorem 5.4.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
theorem positive_mesh_index_tendsto {ι : Type*} {l : Filter ι} {n m : ι → ℕ}
    {t : ℝ} (ht : 0<t) (hn : Tendsto n l atTop)
    (hm : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) : Tendsto m l atTop := by
  have hnR : Tendsto (fun i => (n i:ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := by
    apply (tendsto_congr' ?_).mp (hm.pos_mul_atTop ht hnR)
    filter_upwards [hn.eventually_gt_atTop 0] with i hi
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hi))
  exact tendsto_natCast_atTop_iff.mp hmR

/-- An actual degree power law transfers to every positive moving mesh
with its exact physical power and original amplitude.
Article: jacobi, Theorem 5.4.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
theorem power_mesh_limit (f : ℕ → ℝ) {p A : ℝ}
    (hf : Tendsto (fun k : ℕ => f k/(k:ℝ)^p) atTop (𝓝 A))
    {ι : Type*} {l : Filter ι} {n m : ι → ℕ} {t : ℝ}
    (ht : 0<t) (hn : Tendsto n l atTop)
    (hm : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => f (m i)/(n i:ℝ)^p) l (𝓝 (A*t^p)) := by
  have hmT := positive_mesh_index_tendsto ht hn hm
  have h := (hf.comp hmT).mul (hm.rpow_const (p := p) (Or.inl ht.ne'))
  apply h.congr'
  filter_upwards [hn.eventually_gt_atTop 0,hmT.eventually_gt_atTop 0] with i hni hmi
  have hnR : (0:ℝ)<n i := Nat.cast_pos.mpr hni
  have hmR : (0:ℝ)<m i := Nat.cast_pos.mpr hmi
  simp only [Function.comp_def]
  rw [div_rpow hmR.le hnR.le]
  field_simp [(rpow_pos_of_pos hmR p).ne',(rpow_pos_of_pos hnR p).ne']

/-- The reciprocal scaled mesh converges whenever the genuine power
constant is nonzero. It controls the true standard Green tail summands.
Article: jacobi, Theorem 5.4.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
theorem reciprocal_power_mesh_limit (f : ℕ → ℝ) {p A : ℝ} (hA : A≠0)
    (hf : Tendsto (fun k : ℕ => f k/(k:ℝ)^p) atTop (𝓝 A))
    {ι : Type*} {l : Filter ι} {n m : ι → ℕ} {t : ℝ}
    (ht : 0<t) (hn : Tendsto n l atTop)
    (hm : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => (n i:ℝ)^p/f (m i)) l (𝓝 (1/(A*t^p))) := by
  simpa only [inv_div,one_div] using (power_mesh_limit f hf ht hn hm).inv₀
    (mul_ne_zero hA (rpow_pos_of_pos ht p).ne')

end
end jacobi.Analysis
