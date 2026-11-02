import jacobi.Variational.LocalCompactness

/-!
Article: jacobi, Lemma D.1.
Almost-everywhere convergence of symmetric decreasing densities with common
mass and energy bounds implies convergence of the actual G_2 and G_∞.
Local L1 convergence and the proved uniform spectral tail bounds are assembled
here. This proves continuity along a given convergent sequence; Compactness
then supplies the subsequence to which this theorem applies.
Use: applies the spectral stability theorem to the local compactness limit.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Local L1 distance equals the global L1 distance between the truncated densities.
Use: applies the spectral stability theorem to the local compactness limit.
Article: jacobi, Lemma D.1.
Proof: the difference of the two indicators is the indicator of the difference. -/
theorem truncation_distance (m q : Density) (R : ℝ) :
    (∫ x, |(m.truncate R).value x-(q.truncate R).value x|) =
      ∫ x in Icc (-R) R, |m.value x-q.value x| := by
  have he : (fun x => |(m.truncate R).value x-(q.truncate R).value x|) =
      (Icc (-R) R).indicator (fun x => |m.value x-q.value x|) := by
    funext x
    by_cases hx : x ∈ Icc (-R) R <;> simp [Density.truncate,hx]
  rw [he,integral_indicator measurableSet_Icc]

/-- A common mass bound controls both observations by the same L1 modulus.
Use: converts local L1 convergence into convergence of each truncated observation.
Article: jacobi, Lemma D.1.
Proof: combine the actual spectral stability bounds and use mass(m),mass(q)≤M. -/
theorem observation_distance_le (m q : Density) {M : ℝ} (hm : m.mass ≤ M) (hq : q.mass ≤ M)
    (i : Observation) :
    |observe m i-observe q i| ≤ (2*M+1)*(∫ x, |m.value x-q.value x|) := by
  -- One modulus handles the finite observation set, including the zero-mass case.
  have hM0 : 0 ≤ M := (integral_nonneg m.nonneg).trans hm
  have hdist : 0 ≤ ∫ x, |m.value x-q.value x| := integral_nonneg (fun x => abs_nonneg _)
  cases i with
  | second =>
    have h := kernel_square_distance m.integrable q.integrable m.nonneg q.nonneg
    change |observe m .second-observe q .second| ≤
      (m.mass+q.mass)*(∫ x, |m.value x-q.value x|) at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hdist)
  | top =>
    have h := kernel_top_distance m.integrable q.integrable m.nonneg q.nonneg
    change |observe m .top-observe q .top| ≤ (∫ x, |m.value x-q.value x|) at h
    exact h.trans (le_mul_of_one_le_left hdist (by linarith))

/-- A single explicit tail modulus controls both actual spectral observations.
Use: the uniform approximation argument removes truncation after the local limit.
Article: jacobi, Lemma D.1.
Proof: combine the stronger M²/R second-moment bound and the printed M/R top bound. -/
theorem observation_truncation_le (m : Density) (hs : SymmetricDecreasing m.value)
    {M R : ℝ} (hM : m.mass ≤ M) (hR : 0 < R) (i : Observation) :
    |observe m i-observe (m.truncate R) i| ≤ (M^2+M)/R := by
  -- Nonnegative mass lets both tail estimates use the same numerator M²+M.
  have hM0 : 0 ≤ M := (integral_nonneg m.nonneg).trans hM
  cases i with
  | second =>
    exact (second_truncation_bound m hs hM hR).2.trans
      (div_le_div_of_nonneg_right (by linarith) hR.le)
  | top =>
    obtain ⟨hn,hb⟩ := top_truncation_bound m hs hM hR
    rw [abs_of_nonneg hn]
    exact hb.trans (div_le_div_of_nonneg_right (by nlinarith [sq_nonneg M]) hR.le)

/-- Uniform O(1/R) approximation transfers convergent truncations to the full limit.
Use: the final epsilon argument in the spectral part of Compactness.
Article: jacobi, Lemma D.1.
Source: the three-term triangle inequality and the definition of convergence.
Proof: choose R with C/R<ε/4 and bound the middle, convergent term by ε/2. -/
theorem tendsto_of_uniform_truncations {f : ℕ → ℝ} {a C : ℝ}
    (hC : 0 ≤ C) (F : ℝ → ℕ → ℝ) (A : ℝ → ℝ)
    (hf : ∀ R > 0, ∀ n, |f n-F R n| ≤ C/R)
    (ha : ∀ R > 0, |a-A R| ≤ C/R)
    (hlim : ∀ R > 0, Tendsto (F R) atTop (𝓝 (A R))) : Tendsto f atTop (𝓝 a) := by
  -- Choose the truncation once for each epsilon, then use only its ordinary scalar limit.
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let R := 4*C/ε+1
  have hR : 0 < R := by dsimp [R]; positivity
  have he : R*ε=4*C+ε := by dsimp [R]; field_simp
  have hsmall : C/R < ε/4 := (div_lt_iff₀ hR).mpr (by nlinarith)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hlim R hR) (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hmiddle : |F R n-A R| < ε/2 := by simpa only [Real.dist_eq] using hN n hn
  have htriangle : |f n-a| ≤ |f n-F R n|+|F R n-A R|+|A R-a| := by
    calc
      _ = |(f n-F R n)+(F R n-A R)+(A R-a)| := by congr 1; ring
      _ ≤ _ := (abs_add_le ((f n-F R n)+(F R n-A R)) (A R-a)).trans
        (add_le_add (abs_add_le (f n-F R n) (F R n-A R)) le_rfl)
  rw [Real.dist_eq]
  have hlast : |A R-a| ≤ C/R := by simpa only [abs_sub_comm] using ha R hR
  linarith [hf R hR n]

/-- The genuine second and top spectral observations survive the compactness limit.
Use: preserves active lower spectral constraints in the direct variational argument.
Article: jacobi, Lemma D.1.
Proof: local dominated convergence controls the truncated observations; the proved
spectral tail estimates make their error uniformly arbitrarily small. -/
theorem spectral_observation_limit (m : ℕ → Density) (q : Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) (hqs : SymmetricDecreasing q.value)
    {M E : ℝ} (hM : ∀ n, (m n).mass ≤ M) (hqM : q.mass ≤ M)
    (hE : ∀ n, (m n).energy ≤ E) (hqE : q.energy ≤ E)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x))) (i : Observation) :
    Tendsto (fun n => observe (m n) i) atTop (𝓝 (observe q i)) := by
  -- The same finite-energy limit and the same truncations are used for both observations.
  have hM0 : 0 ≤ M := (integral_nonneg (m 0).nonneg).trans (hM 0)
  apply tendsto_of_uniform_truncations (C := M^2+M) (by positivity)
    (fun R n => observe ((m n).truncate R) i) (fun R => observe (q.truncate R) i)
  · exact fun R hR n => observation_truncation_le (m n) (hs n) (hM n) hR i
  · exact fun R hR => observation_truncation_le q hqs hqM hR i
  · intro R _hR
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hl := (local_l1_limit m q hs hqs hE hqE hlim R).const_mul (2*M+1)
    simp only [mul_zero] at hl
    apply squeeze_zero (fun _ => norm_nonneg _) _ hl
    intro n
    rw [Real.norm_eq_abs]
    have h := observation_distance_le ((m n).truncate R) (q.truncate R)
      (((m n).truncate_mass_le R).trans (hM n)) ((q.truncate_mass_le R).trans hqM) i
    rwa [truncation_distance] at h

end
end jacobi.Variational
