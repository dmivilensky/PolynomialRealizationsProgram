import chebyshev2.Continuum.SpectralOrder

/-!
Article: chebyshev2, Theorem 2.3.
A finite eigenframe gives a lower bound for the sorted eigenvalue, including comparison between
Hilbert spaces of different dimensions.
Use: `chebyshev2.Continuum.eigenvalue_ge_of_eigenframe` feeds
`chebyshev2.Continuum.gram_eigenvalue_le` (gram eigenvalue le).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open Submodule Module
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The stated quantitative bound `r * ‖x‖^2 ≤ inner ℝ x (T x)`.

Use: `chebyshev2.Continuum.eigenvalue_ge_of_eigenframe` uses this bound to establish the
stated quantitative bound `r ≤ D.eigenvalue n`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem eigenframe_span_lower {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal ℝ v)
    (T : E →L[ℝ] E) {eig : ι → ℝ} (he : ∀ i, T (v i) = eig i • v i)
    {r : ℝ} (hr : ∀ i, r ≤ eig i) (x : E) (hx : x ∈ span ℝ (Set.range v)) :
    r * ‖x‖^2 ≤ inner ℝ x (T x) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  obtain ⟨c,hc⟩ := (mem_span_range_iff_exists_fun ℝ).mp hx
  change (∑ i, c i • v i) = x at hc
  have hT : T x = ∑ i, (c i * eig i) • v i := by
    rw [← hc,map_sum]
    simp only [map_smul,he,smul_smul]
  have hnorm : ‖x‖^2 = ∑ i, c i^2 := by
    rw [← real_inner_self_eq_norm_sq,← hc,hv.inner_sum]
    simp only [conj_trivial,pow_two]
  rw [hT,← hc,hv.inner_sum]
  rw [← hc] at hnorm
  rw [hnorm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [conj_trivial]
  nlinarith [mul_le_mul_of_nonneg_right (hr i) (sq_nonneg (c i))]

/--
A finite eigenframe gives a lower bound for the sorted eigenvalue, including comparison between
Hilbert spaces of different dimensions.

The stated quantitative bound `r ≤ D.eigenvalue n`.

Use: `chebyshev2.Continuum.gram_eigenvalue_le` uses this bound to establish the stated
quantitative bound `D.eigenvalue n ≤ D'.eigenvalue n`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem eigenvalue_ge_of_eigenframe {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    {ι : Type*} [Fintype ι] {v : ι → E} (hv : Orthonormal ℝ v) {eig : ι → ℝ}
    (he : ∀ i, T (v i) = eig i • v i) {r : ℝ} (hr : ∀ i, r ≤ eig i)
    (n : ℕ) (hn : n < Fintype.card ι) : r ≤ D.eigenvalue n := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  by_contra! hlt
  let s := spectralSelected D.summable n
  let S := span ℝ (Set.range v)
  let φ : S →ₗ[ℝ] (s → ℝ) := LinearMap.pi (fun i => ((innerSL ℝ (D.basis i)).toLinearMap).comp S.subtype)
  have hdim : finrank ℝ S = Fintype.card ι := finrank_span_eq_card hv.linearIndependent
  have hdim' : finrank ℝ (s → ℝ) ≤ n := by
    rw [Module.finrank_pi]
    simpa using spectralSelected_card_le D.summable n
  have hker : φ.ker ≠ ⊥ := by
    intro h
    have hh := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    rw [hdim] at hh
    omega
  obtain ⟨x,hx,hxne⟩ := φ.ker.ne_bot_iff.mp hker
  have horth : ∀ i ∈ spectralSelected D.summable n, inner ℝ (D.basis i) (x : E) = 0 := by
    intro i hi
    exact congrFun (LinearMap.mem_ker.mp hx) (⟨i,hi⟩ : s)
  have hlow := eigenframe_span_lower hv T he hr (x : E) x.property
  have hhigh := D.quadratic_le_eigenvalue n (x : E) horth
  have hne : (x : E) ≠ 0 := fun h => hxne (Subtype.ext h)
  have hnorm : 0 < ‖(x : E)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  nlinarith

end
end chebyshev2.Continuum
