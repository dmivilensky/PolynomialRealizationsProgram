import krylov.XR.ConditionalCompletion

/-!
Article: main_krylov, prop:cond(a), exact attained known-base radius.
Use: maximize the true hidden diagonal over the genuine symmetric spectral
completion fibre, including its singular Schur endpoints. Source: the
proved exact scalar Schur interval and elementary endpoint maximization.
-/

/-!
Article: krylov, Proposition F.3 [prop:cond].

The true known-base and compressed-data fibres have exact attained conditional radii; actual
two-dimensional physical histories realize them.
Feasibility ellipses, strict defect monotonicity, zero-defect/zero-budget cases and the
equality branch δ=0 are retained by the underlying conditional modules.
-/
namespace krylov.XR
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Zero cross information gives the literal diagonal completion norm.
Article: main_krylov, prop:cond, boundary pivot case. -/
theorem conditionalMatrix_zero_cross_iff (y k ω : ℝ) (hω : 0≤ω) :
    ‖conditionalMatrix y 0 k‖≤ω ↔ |y|≤ω ∧ |k|≤ω := by
  have he : conditionalMatrix y 0 k=diagonal (![y,k] : Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conditionalMatrix]
  rw [he,Matrix.l2_opNorm_diagonal,pi_norm_le_iff_of_nonneg hω]
  simp [Fin.forall_fin_two,Real.norm_eq_abs]

/-- Genuine feasibility makes the original strict Schur interval
nonempty; the full spectral endpoint completions therefore exist.
Article: main_krylov, prop:cond(a). -/
theorem conditional_schur_interval_nonempty {ω δ k : ℝ} (hk : |k|<ω)
    (hfeasible : δ^2+k^2≤ω^2) :
    -ω+δ^2/(ω+k)≤ω-δ^2/(ω-k) := by
  have hp : 0<ω+k := by linarith [(abs_lt.mp hk).1]
  have hm : 0<ω-k := by linarith [(abs_lt.mp hk).2]
  have hω : 0<ω := (abs_nonneg k).trans_lt hk
  have he : (ω-δ^2/(ω-k))-(-ω+δ^2/(ω+k))=
      2*ω*(ω^2-k^2-δ^2)/((ω+k)*(ω-k)) := by field_simp; ring
  have hh : 0≤2*ω*(ω^2-k^2-δ^2)/((ω+k)*(ω-k)) := by
    apply div_nonneg
    · exact mul_nonneg (by positivity) (by linarith)
    · positivity
  linarith

/-- The exact attained hidden-diagonal maximum on the true strict-pivot
spectral completion fibre. Article: main_krylov, prop:cond(a). -/
theorem knownConditionalFibre_strict {ω δ k : ℝ} (hk : |k|<ω)
    (hfeasible : δ^2+k^2≤ω^2) :
    IsGreatest {r : ℝ | ∃ y : ℝ,‖conditionalMatrix y δ k‖≤ω ∧ r=|y|}
      (ω-δ^2/(ω+|k|)) := by
  have hp : 0<ω+k := by linarith [(abs_lt.mp hk).1]
  have hm : 0<ω-k := by linarith [(abs_lt.mp hk).2]
  have hab := conditional_schur_interval_nonempty hk hfeasible
  by_cases hkn : 0≤k
  · rw [abs_of_nonneg hkn]
    have hdiv : δ^2/(ω+k)≤δ^2/(ω-k) :=
      div_le_div_of_nonneg_left (sq_nonneg δ) hm (by linarith)
    have hlo : -ω+δ^2/(ω+k)≤0 := by linarith
    constructor
    · refine ⟨-ω+δ^2/(ω+k),(conditionalMatrix_norm_iff _ _ _ _ hk).mpr ⟨le_rfl,hab⟩,?_⟩
      rw [abs_of_nonpos hlo]
      ring
    · rintro r ⟨y,hy,rfl⟩
      obtain ⟨hl,hu⟩ := (conditionalMatrix_norm_iff y δ k ω hk).mp hy
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  · have hkn' : k≤0 := (lt_of_not_ge hkn).le
    rw [abs_of_nonpos hkn',←sub_eq_add_neg]
    have hdiv : δ^2/(ω-k)≤δ^2/(ω+k) :=
      div_le_div_of_nonneg_left (sq_nonneg δ) hp (by linarith)
    have hhi : 0≤ω-δ^2/(ω-k) := by linarith
    constructor
    · refine ⟨ω-δ^2/(ω-k),(conditionalMatrix_norm_iff _ _ _ _ hk).mpr ⟨hab,le_rfl⟩,?_⟩
      rw [abs_of_nonneg hhi]
    · rintro r ⟨y,hy,rfl⟩
      obtain ⟨hl,hu⟩ := (conditionalMatrix_norm_iff y δ k ω hk).mp hy
      apply abs_le.mpr
      constructor <;> linarith

/-- The original known-base hidden radius is the exact actual maximum,
including the singular boundary k=+-omega and delta=0.
Article: main_krylov, prop:cond(a). -/
theorem knownConditionalFibre {ω δ k : ℝ} (hω : 0<ω)
    (hfeasible : δ^2+k^2≤ω^2) :
    IsGreatest {r : ℝ | ∃ y : ℝ,‖conditionalMatrix y δ k‖≤ω ∧ r=|y|}
      (ω-δ^2/(ω+|k|)) := by
  have hk : |k|≤ω := by nlinarith [sq_abs k,abs_nonneg k,sq_nonneg δ]
  rcases lt_or_eq_of_le hk with hlt|heq
  · exact knownConditionalFibre_strict hlt hfeasible
  · have hd : δ=0 := by nlinarith [sq_abs k]
    rw [hd]
    norm_num
    constructor
    · exact ⟨ω,(conditionalMatrix_zero_cross_iff ω k ω hω.le).mpr ⟨by rw [abs_of_pos hω],hk⟩,
        (abs_of_pos hω).symm⟩
    · rintro r ⟨y,hy,rfl⟩
      exact ((conditionalMatrix_zero_cross_iff y k ω hω.le).mp hy).1

end
end krylov.XR
