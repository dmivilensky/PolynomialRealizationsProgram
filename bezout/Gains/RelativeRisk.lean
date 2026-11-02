import bezout.Gains.Bounds
import Mathlib.Topology.Order.LiminfLimsup

/-!
Article: bezout, the literal supremum and positive-scale upper-limit definition
of the local relative gain in Theorem 4.1.
Use: connects actual noisy-query execution risk to `Filter.limsup`; the supremum
over dimensions and errors is taken at each scale before taking the limit.
Proof: finite uniform majorants make every scale risk finite and attained as a
least upper bound; the uniform quadratic remainder supplies eventual boundedness.
-/

namespace bezout.Gains
noncomputable section
open Polynomial Filter Topology
open scoped BigOperators
variable {N : ℕ}

/-- A bound on the actual relative-error response at one fixed error scale. -/
def RelativeBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E), Analysis.Admissible I H →
    ∀ (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
      (δ : Fin N → ℝ), ‖initial‖ ≤ 1 → Analysis.RelativeErrors h H initial noise u t δ →
      ‖u.output - (aeval H h.terminal) initial‖ ≤ C

/-- The actual finite-scale worst relative response over all finite Hilbert spaces. -/
def relativeRisk (h : bezout.History N) (I : chebyshev1.SpectralInterval) (t : ℝ) : ℝ :=
  sInf {C : ℝ | RelativeBound h I t C}

/-- Every universal finite-scale bound is nonnegative, including negative scales. -/
theorem relativeBound_nonneg (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t C : ℝ) (hb : RelativeBound h I t C) : 0 ≤ C := by
  let H := bezout.History.scalarOperator I.mu
  let u := h.run H 0 (fun _ => 0)
  have hu := hb ℝ H (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩)
    0 (fun _ => 0) u (fun _ => 0) (by simp) ⟨by simp, by simp, by simp⟩
  exact (norm_nonneg _).trans hu

/-- A relative-error stream at any scale is admissible at its absolute scale. -/
theorem relativeErrors_abs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
    (t : ℝ) (δ : Fin N → ℝ) (hw : Analysis.RelativeErrors h H initial noise u t δ) :
    Analysis.RelativeErrors h H initial noise u |t| δ := by
  refine ⟨hw.1, hw.2.1, fun s => (hw.2.2 s).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self t) (hw.1 s)) (norm_nonneg _)

/-- Product certificates bound the actual finite-scale response including its remainder. -/
theorem relativeBound_of_product_bounds (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s)
    {t t0 : ℝ} (ht : 0 ≤ t) (htt0 : t ≤ t0) :
    RelativeBound h I t (t * Analysis.energyNorm (fun s => P s * Q s) +
      t ^ 2 * Analysis.energyNorm (fun s => P s * Analysis.deviationMajorant h I.L t0 s)) := by
  intro E _ _ _ H hH initial noise u δ hi hw
  simpa only [mul_one] using Analysis.relative_response_bound h I H hH initial noise u
    1 t t0 zero_le_one ht htt0 hi δ hw P Q hP hQ hq

/-- Every fixed-scale actual relative risk is a finite real least upper bound. -/
theorem relativeBounds_nonempty (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t : ℝ) : {C : ℝ | RelativeBound h I t C}.Nonempty := by
  obtain ⟨P, Q, hP, hQ, hq⟩ := exists_product_bounds h I
  refine ⟨|t| * Analysis.energyNorm (fun s => P s * Q s) +
    |t| ^ 2 * Analysis.energyNorm (fun s => P s * Analysis.deviationMajorant h I.L |t| s), ?_⟩
  intro E _ _ _ H hH initial noise u δ hi hw
  exact relativeBound_of_product_bounds h I P Q hP hQ hq (abs_nonneg t) le_rfl
    E H hH initial noise u δ hi (relativeErrors_abs h H initial noise u t δ hw)

/-- The finite-scale risk is nonnegative. -/
theorem relativeRisk_nonneg (h : bezout.History N) (I : chebyshev1.SpectralInterval) (t : ℝ) :
    0 ≤ relativeRisk h I t :=
  le_csInf (relativeBounds_nonempty h I t) (fun C hb => relativeBound_nonneg h I t C hb)

/-- Every finite universal bound bounds the supremal risk. -/
theorem relativeRisk_le (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t C : ℝ) (hb : RelativeBound h I t C) : relativeRisk h I t ≤ C :=
  csInf_le ⟨0, fun B hB => relativeBound_nonneg h I t B hB⟩ hb

/-- The least universal bound is itself a bound on every actual admissible execution. -/
theorem relativeRisk_isBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t : ℝ) : RelativeBound h I t (relativeRisk h I t) := by
  intro E _ _ _ H hH initial noise u δ hi hw
  exact le_csInf (relativeBounds_nonempty h I t) (fun C hb => hb E H hH initial noise u δ hi hw)

/-- Fixed-scale universal bounds and the literal supremal risk are equivalent. -/
theorem relativeBound_iff (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (t C : ℝ) : RelativeBound h I t C ↔ relativeRisk h I t ≤ C := by
  constructor
  · exact relativeRisk_le h I t C
  · intro hc E _ _ _ H hH initial noise u δ hi hw
    exact (relativeRisk_isBound h I t E H hH initial noise u δ hi hw).trans hc

/-- The neighborhood definition used by the gain is exactly a bound on normalized scale risk. -/
theorem localRelativeBound_iff_risk (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (C : ℝ) : LocalRelativeBound h I C ↔
      ∀ ε : ℝ, 0 < ε → ∃ t0 : ℝ, 0 < t0 ∧
        ∀ t : ℝ, 0 < t → t < t0 → relativeRisk h I t / t ≤ C + ε := by
  constructor
  · intro hc ε hε
    obtain ⟨t0, ht0, hbound⟩ := hc ε hε
    refine ⟨t0, ht0, fun t ht htt => ?_⟩
    apply (div_le_iff₀ ht).mpr
    rw [mul_comm]
    exact relativeRisk_le h I t _ (hbound t ht htt)
  · intro hc ε hε
    obtain ⟨t0, ht0, hbound⟩ := hc ε hε
    refine ⟨t0, ht0, fun t ht htt => ?_⟩
    apply (relativeBound_iff h I t _).mpr
    have hh := (div_le_iff₀ ht).mp (hbound t ht htt)
    simpa only [mul_comm] using hh

/-- The normalized scale risk has a uniform finite upper bound near zero. -/
theorem normalizedRisk_bounded (h : bezout.History N) (I : chebyshev1.SpectralInterval) :
    (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) (fun t => relativeRisk h I t / t) := by
  obtain ⟨P, Q, hP, hQ, hq⟩ := exists_product_bounds h I
  let A := Analysis.energyNorm (fun s => P s * Q s)
  let B := Analysis.energyNorm (fun s => P s * Analysis.deviationMajorant h I.L 1 s)
  apply Filter.isBoundedUnder_of_eventually_le (a := A + B)
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨1, by norm_num, fun t ht => ?_⟩
  have hb := relativeRisk_le h I t _
    (relativeBound_of_product_bounds h I P Q hP hQ hq ht.1.le ht.2.le)
  have hB : 0 ≤ B := Analysis.energyNorm_nonneg _
  apply (div_le_iff₀ ht.1).mpr
  change relativeRisk h I t ≤ (A + B) * t
  change relativeRisk h I t ≤ t * A + t ^ 2 * B at hb
  have hterm : t ^ 2 * B ≤ t * B :=
    mul_le_mul_of_nonneg_right (by nlinarith [ht.1, ht.2]) hB
  nlinarith

/-- Nonnegative scale risks also prevent the real upper limit from escaping below. -/
theorem normalizedRisk_cobounded (h : bezout.History N) (I : chebyshev1.SpectralInterval) :
    (𝓝[>] (0 : ℝ)).IsCoboundedUnder (· ≤ ·) (fun t => relativeRisk h I t / t) := by
  apply Filter.isCoboundedUnder_le_of_eventually_le (𝓝[>] (0 : ℝ)) (x := 0)
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  exact ⟨1, by norm_num, fun t ht => div_nonneg (relativeRisk_nonneg h I t) ht.1.le⟩

/-- The asymptotic comparison predicate is exactly an upper bound on the literal limsup. -/
theorem localRelativeBound_iff_limsup (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (C : ℝ) : LocalRelativeBound h I C ↔
      Filter.limsup (fun t => relativeRisk h I t / t) (𝓝[>] (0 : ℝ)) ≤ C := by
  rw [localRelativeBound_iff_risk, Filter.limsup_le_iff'
    (normalizedRisk_cobounded h I) (normalizedRisk_bounded h I)]
  constructor
  · intro hc y hy
    obtain ⟨t0, ht0, hb⟩ := hc (y - C) (sub_pos.mpr hy)
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    refine ⟨t0, ht0, fun t ht => ?_⟩
    have hh := hb t ht.1 ht.2
    change relativeRisk h I t / t ≤ y
    linarith
  · intro hc ε hε
    have hh := hc (C + ε) (by linarith)
    obtain ⟨t0, ht0, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hh
    exact ⟨t0, ht0, fun t ht htt => hb ⟨ht, htt⟩⟩

/-- The formal local gain equals the article's literal positive-scale limsup of supremal risk. -/
theorem localRelativeGain_eq_limsup (h : bezout.History N) (I : chebyshev1.SpectralInterval) :
    localRelativeGain h I = Filter.limsup (fun t => relativeRisk h I t / t) (𝓝[>] (0 : ℝ)) := by
  have hs : {C : ℝ | LocalRelativeBound h I C} =
      Set.Ici (Filter.limsup (fun t => relativeRisk h I t / t) (𝓝[>] (0 : ℝ))) := by
    ext C
    exact localRelativeBound_iff_limsup h I C
  unfold localRelativeGain
  rw [hs, csInf_Ici]

section Homogeneity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale every state and physical error in one actual execution by the same scalar. -/
def scaleExecution (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (c : ℝ) :
    h.Execution H (c • initial) (fun s => c • noise s) where
  query s := c • u.query s
  answer s := c • u.answer s
  query_eq s := by
    rw [u.query_eq]
    simp only [smul_sub, Finset.smul_sum, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  answer_eq s := by rw [u.answer_eq, smul_add, map_smul]

/-- The physical terminal scales with the actual execution. -/
theorem scaleExecution_output (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (c : ℝ) :
    (scaleExecution h H initial noise u c).output = c • u.output := by
  simp only [bezout.History.Execution.output, scaleExecution, smul_sub,
    Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

/-- Relative-error feasibility is preserved by positive radial scaling. -/
theorem relativeErrors_scale (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
    (t : ℝ) (δ : Fin N → ℝ) (hw : Analysis.RelativeErrors h H initial noise u t δ)
    (c : ℝ) (hc : 0 ≤ c) :
    Analysis.RelativeErrors h H (c • initial) (fun s => c • noise s)
      (scaleExecution h H initial noise u c) t δ := by
  refine ⟨hw.1, hw.2.1, fun s => ?_⟩
  change ‖c • noise s‖ ≤ t * δ s * ‖c • u.query s‖
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have hh := mul_le_mul_of_nonneg_left (hw.2.2 s) hc
  nlinarith

/-- Normalized deviation risk is homogeneous in the initial radius. -/
theorem scaleExecution_error (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (c : ℝ) :
    ‖(scaleExecution h H initial noise u c).output - (aeval H h.terminal) (c • initial)‖ =
      |c| * ‖u.output - (aeval H h.terminal) initial‖ := by
  rw [scaleExecution_output, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]

end Homogeneity

/-- The literal finite-scale relative-response bound at an arbitrary initial radius. -/
def RelativeRadiusBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t C : ℝ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E), Analysis.Admissible I H →
    ∀ (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
      (δ : Fin N → ℝ), ‖initial‖ ≤ r → Analysis.RelativeErrors h H initial noise u t δ →
      ‖u.output - (aeval H h.terminal) initial‖ ≤ C

/-- Exact positive-radius reduction to the unit-radius actual execution risk. -/
theorem relativeRadiusBound_iff (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t C : ℝ) (hr : 0 < r) : RelativeRadiusBound h I r t (r * C) ↔ RelativeBound h I t C := by
  constructor
  · intro hb E _ _ _ H hH initial noise u δ hi hw
    have hs : ‖r • initial‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hr.le
    have hu := hb E H hH (r • initial) (fun s => r • noise s)
      (scaleExecution h H initial noise u r) δ hs (relativeErrors_scale h H initial noise u t δ hw r hr.le)
    rw [scaleExecution_error, abs_of_pos hr] at hu
    exact (mul_le_mul_iff_right₀ hr).mp hu
  · intro hb E _ _ _ H hH initial noise u δ hi hw
    have hc : 0 < 1 / r := one_div_pos.mpr hr
    have hs : ‖(1 / r) • initial‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      have hh := mul_le_mul_of_nonneg_left hi hc.le
      simpa only [one_div_mul_cancel (ne_of_gt hr)] using hh
    have hu := hb E H hH ((1 / r) • initial) (fun s => (1 / r) • noise s)
      (scaleExecution h H initial noise u (1 / r)) δ hs
      (relativeErrors_scale h H initial noise u t δ hw (1 / r) hc.le)
    rw [scaleExecution_error, abs_of_pos hc, one_div_mul_eq_div] at hu
    exact (div_le_iff₀ hr).mp hu |>.trans_eq (mul_comm C r)

/-- The finite-scale actual relative risk with a specified initial radius. -/
def relativeRadiusRisk (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) : ℝ := sInf {C : ℝ | RelativeRadiusBound h I r t C}

/-- Every positive-radius finite-scale risk has a finite universal bound. -/
theorem relativeRadiusBounds_nonempty (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) (hr : 0 < r) : {C : ℝ | RelativeRadiusBound h I r t C}.Nonempty :=
  ⟨r * relativeRisk h I t, (relativeRadiusBound_iff h I r t _ hr).mpr (relativeRisk_isBound h I t)⟩

/-- A nonnegative initial radius always includes the zero physical execution. -/
theorem relativeRadiusBound_nonneg (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t C : ℝ) (hr : 0 ≤ r) (hb : RelativeRadiusBound h I r t C) : 0 ≤ C := by
  let H := bezout.History.scalarOperator I.mu
  let u := h.run H 0 (fun _ => 0)
  have hu := hb ℝ H (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩)
    0 (fun _ => 0) u (fun _ => 0) (by simpa using hr) ⟨by simp, by simp, by simp⟩
  exact (norm_nonneg _).trans hu

/-- The positive-radius supremal risk bounds every actual execution. -/
theorem relativeRadiusRisk_isBound (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) (hr : 0 < r) : RelativeRadiusBound h I r t (relativeRadiusRisk h I r t) := by
  intro E _ _ _ H hH initial noise u δ hi hw
  exact le_csInf (relativeRadiusBounds_nonempty h I r t hr)
    (fun C hb => hb E H hH initial noise u δ hi hw)

/-- Exact positive homogeneity of the literal supremal relative response. -/
theorem relativeRadiusRisk_eq (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (r t : ℝ) (hr : 0 < r) : relativeRadiusRisk h I r t = r * relativeRisk h I t := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun C hb => relativeRadiusBound_nonneg h I r t C hr.le hb⟩
      ((relativeRadiusBound_iff h I r t _ hr).mpr (relativeRisk_isBound h I t))
  · have hb := relativeRadiusRisk_isBound h I r t hr
    have hs : r * (relativeRadiusRisk h I r t / r) = relativeRadiusRisk h I r t := by
      field_simp
    rw [← hs] at hb
    have hu := (relativeRadiusBound_iff h I r t (relativeRadiusRisk h I r t / r) hr).mp hb
    have hu' := relativeRisk_le h I t _ hu
    have hh := (le_div_iff₀ hr).mp hu'
    simpa only [mul_comm] using hh

/-- The literal article limit is independent of every positive initial radius. -/
theorem localRelativeGain_eq_radius_limsup (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (r : ℝ) (hr : 0 < r) :
    localRelativeGain h I =
      Filter.limsup (fun t => relativeRadiusRisk h I r t / (t * r)) (𝓝[>] (0 : ℝ)) := by
  rw [localRelativeGain_eq_limsup]
  apply Filter.limsup_congr
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨1, by norm_num, fun t ht => ?_⟩
  change relativeRisk h I t / t = relativeRadiusRisk h I r t / (t * r)
  rw [relativeRadiusRisk_eq h I r t hr]
  field_simp

end
end bezout.Gains
