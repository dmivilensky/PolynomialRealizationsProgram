import nesterov.Duality.Separation

/-! Finite strict certificates persist under simultaneous changes of both
amplitudes and the exponent. The same lag multipliers work, with the two
minimizer charges adjusted continuously to restore exact cancellation. -/
noncomputable section
open scoped Topology BigOperators
namespace nesterov.Duality
open Spectral

theorem continuous_symbol_family {X : Type*} [TopologicalSpace X]
    {m : X → SymbolPair} {t gp gm : X → ℝ}
    (hu : Continuous (fun x => (m x).u)) (hp : Continuous (fun x => (m x).p))
    (ht : Continuous t) (hgp : Continuous gp) (hgm : Continuous gm)
    (lags : Finset ℕ) (α β : ℕ → ℝ) :
    Continuous (fun q : X × Frequency => symbol (m q.1) (t q.1) lags α β
      (gp q.1) (gm q.1) q.2) := by
  have hu' := continuous_eval.comp ((hu.comp continuous_fst).prodMk continuous_snd)
  have hp' := continuous_eval.comp ((hp.comp continuous_fst).prodMk continuous_snd)
  have hg : Continuous (fun q : X × Frequency => g (m q.1) q.2) :=
    (Complex.continuous_normSq.comp hu').sub (Complex.continuous_normSq.comp hp')
  have hs : Continuous (fun q : X × Frequency => skew (m q.1) q.2) :=
    Complex.continuous_im.comp (hp'.mul hu'.star)
  have hA (n : ℕ) : Continuous (fun q : X × Frequency => lagA (m q.1) (t q.1) n q.2) := by
    unfold lagA
    exact hg.mul ((Real.continuous_cosh.comp (continuous_const.mul (ht.comp continuous_fst))).sub
      (Real.continuous_cos.comp (continuous_const.mul
        (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd)))))
  have hB (n : ℕ) : Continuous (fun q : X × Frequency => lagB (m q.1) n q.2) := by
    unfold lagB
    exact (continuous_const.mul hs).mul (Real.continuous_sin.comp (continuous_const.mul
      (Real.continuous_arccos.comp (continuous_subtype_val.comp continuous_snd))))
  unfold symbol
  exact (continuous_finsetSum _ (fun n _ =>
    (continuous_const.mul ((hA n).sub (hB n))).add
      (continuous_const.mul ((hA n).add (hB n))))).add
    (((hgp.comp continuous_fst).add (hgm.comp continuous_fst)).mul hg)

/-- A certificate keeps all its lag weights and a positive uniform margin locally. -/
theorem StrictCertificate.eventually {X : Type*} [TopologicalSpace X]
    {m : X → SymbolPair} {t : X → ℝ} {x₀ : X}
    (cert : StrictCertificate (m x₀) (t x₀))
    (hu : Continuous (fun x => (m x).u)) (hp : Continuous (fun x => (m x).p))
    (ht : Continuous t) :
    ∀ᶠ x in 𝓝 x₀, ∃ cert' : StrictCertificate (m x) (t x),
      cert'.lags = cert.lags ∧ cert'.α = cert.α ∧ cert'.β = cert.β ∧
        cert'.ε = cert.ε / 2 := by
  let q : X → ℝ := fun x => (∑ n ∈ cert.lags,
    (cert.α n - cert.β n) * Real.sinh (n * t x)) + cert.γplus - cert.γminus
  let gp : X → ℝ := fun x => cert.γplus + max (-q x) 0
  let gm : X → ℝ := fun x => cert.γminus + max (q x) 0
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hgp : Continuous gp := continuous_const.add (hq.neg.max continuous_const)
  have hgm : Continuous gm := continuous_const.add (hq.max continuous_const)
  have hq₀ : q x₀ = 0 := cert.cancel
  have hgp₀ : gp x₀ = cert.γplus := by simp [gp, hq₀]
  have hgm₀ : gm x₀ = cert.γminus := by simp [gm, hq₀]
  have hs := continuous_symbol_family hu hp ht hgp hgm cert.lags cert.α cert.β
  have hnear : ∀ᶠ x in 𝓝 x₀, ∀ c,
      symbol (m x) (t x) cert.lags cert.α cert.β (gp x) (gm x) c < -cert.ε / 2 := by
    have h := (isCompact_univ : IsCompact (Set.univ : Set Frequency)).eventually_forall_of_forall_eventually
      (P := fun x c => symbol (m x) (t x) cert.lags cert.α cert.β (gp x) (gm x) c < -cert.ε / 2)
      (x₀ := x₀) (fun c _ => hs.continuousAt.eventually (gt_mem_nhds (by
        dsimp only
        rw [hgp₀, hgm₀]
        linarith [cert.strict c, cert.ε_pos])))
    simpa only [Set.mem_univ, forall_true_left] using h
  filter_upwards [hnear] with x hx
  refine ⟨{ cert with
    γplus := gp x
    γminus := gm x
    γplus_nonneg := cert.γplus_nonneg.trans (le_add_of_nonneg_right (le_max_right _ _))
    γminus_nonneg := cert.γminus_nonneg.trans (le_add_of_nonneg_right (le_max_right _ _))
    ε := cert.ε / 2
    ε_pos := half_pos cert.ε_pos
    cancel := ?_
    strict := fun c => by simpa only [neg_div] using (hx c).le }, rfl, rfl, rfl, rfl⟩
  have he : max (-q x) 0 - max (q x) 0 = -q x := by
    rcases le_total (q x) 0 with h | h
    · rw [max_eq_left (neg_nonneg.mpr h), max_eq_right h]
      ring
    · rw [max_eq_right (neg_nonpos.mpr h), max_eq_left h]
      ring
  change (∑ n ∈ cert.lags, (cert.α n - cert.β n) * Real.sinh (n * t x)) +
    (cert.γplus + max (-q x) 0) - (cert.γminus + max (q x) 0) = 0
  dsimp [q] at he
  linarith

/-- The primal-feasible parameter set is closed even when amplitudes vary.
This follows from the proved finite strict alternative and persistence. -/
theorem isClosed_exists_feasible {X : Type*} [TopologicalSpace X]
    {m : X → SymbolPair} {t : X → ℝ}
    (hu : Continuous (fun x => (m x).u)) (hp : Continuous (fun x => (m x).p))
    (ht : Continuous t) : IsClosed {x | ∃ ν C, Feasible (m x) (t x) ν C} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨cert⟩ := (infeasible_iff_strictCertificate (m x) (t x)).mp hx
  filter_upwards [cert.eventually hu hp ht] with y hy
  obtain ⟨cert', _⟩ := hy
  exact (infeasible_iff_strictCertificate (m y) (t y)).mpr ⟨cert'⟩

end nesterov.Duality
