import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
Article: jacobi, Proposition B.1.
A genuine quadratic lower bound up to a fixed additive error and positive
fixed-index limits give one uniform positive quadratic lower bound on an
arbitrarily growing actual finite prefix. The finite initial indices are
handled together using their true limits, not numerical certificates.
Use: discharges every small-index shifted endpoint margin in Proposition B.1 (d), while the genuine quadratic growth handles all remaining indices.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set Filter
open scoped Topology

/-- Positive genuine fixed-index limits upgrade a quadratic lower bound with bounded additive error to a uniform positive quadratic bound on a growing finite index range.
Use: discharges every small-index shifted endpoint margin in Proposition B.1 (d), while the genuine quadratic growth handles all remaining indices.
Article: jacobi, Proposition B.1.
Proof: choose one index threshold at which the fixed additive error is
at most half the quadratic term. The finitely many smaller actual limits
are uniformly above delta; their sequences are simultaneously above
delta/2 at large degree. Take the smaller of the resulting two positive
quadratic constants. -/
theorem uniform_positive_quadratic {P : ℕ → ℕ → Prop} {f : ℕ → ℕ → ℝ} {v : ℕ → ℝ}
    {m B delta : ℝ} (hm : 0<m) (hdelta : 0<delta)
    (hlim : ∀ k,Tendsto (fun n => f n k) atTop (𝓝 (v k))) (hv : ∀ k,delta≤v k)
    (hcoerce : ∀ᶠ n : ℕ in atTop,∀ k,P n k → m*(k+1:ℝ)^2-B≤f n k) :
    ∃ d : ℝ,0<d ∧ ∀ᶠ n : ℕ in atTop,∀ k,P n k → d*(k+1:ℝ)^2≤f n k := by
  -- The finite prefix is controlled by its genuine original limits; no artificial lower-bound data are assumed for individual small indices.
  obtain ⟨K,hK⟩ := exists_nat_gt (2*B/m+1)
  have hKp : 0<(K+1:ℝ) := by positivity
  let d := min (m/2) (delta/(2*(K+1:ℝ)^2))
  have hd : 0<d := lt_min (by positivity) (by positivity)
  have hfinite : ∀ᶠ n : ℕ in atTop,∀ k∈Finset.range K,delta/2≤f n k := by
    apply (Filter.eventually_all_finite (Finset.finite_toSet (Finset.range K))).mpr
    intro k _
    have hlt : delta/2<v k := by linarith [hv k]
    exact ((hlim k).eventually (Ioi_mem_nhds hlt)).mono (fun _ h => h.le)
  refine ⟨d,hd,?_⟩
  filter_upwards [hcoerce,hfinite] with n hn hfn
  intro k hpk
  by_cases hk : k<K
  · have hkt : (k+1:ℝ)≤(K+1:ℝ) := by exact_mod_cast Nat.add_le_add_right hk.le 1
    have hsquare := (sq_le_sq₀ (by positivity : 0≤(k+1:ℝ)) hKp.le).mpr hkt
    have hD : d≤delta/(2*(K+1:ℝ)^2) := min_le_right _ _
    have hh := mul_le_mul hD hsquare (sq_nonneg _) (by positivity : 0≤delta/(2*(K+1:ℝ)^2))
    have he : (delta/(2*(K+1:ℝ)^2))*(K+1:ℝ)^2=delta/2 := by field_simp [hKp.ne']
    rw [he] at hh
    exact hh.trans (hfn k (Finset.mem_range.mpr hk))
  · have hkR : (K:ℝ)≤k := by exact_mod_cast (show K≤k by omega)
    have htail : B≤(m/2)*(k+1:ℝ)^2 := by
      have hBK : 2*B/m<(K:ℝ) := by linarith
      have hdiv := (div_lt_iff₀ hm).mp hBK
      have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
      nlinarith [mul_nonneg hm.le (sq_nonneg (k:ℝ))]
    have hD : d≤m/2 := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_right hD (sq_nonneg (k+1:ℝ))
    have hn' := hn k hpk
    linarith

end
end jacobi.Oscillation
