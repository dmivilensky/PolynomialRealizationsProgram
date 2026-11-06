import nesterov.Duality.Persistence

/-! The precise perturbation statement from the article: only the gap and
skew functions need be uniformly close; the amplitudes themselves may change freely. -/
noncomputable section
open scoped Topology BigOperators
namespace nesterov.Duality
open Spectral

def symbolGS (G S : C(Frequency, ℝ)) (t : ℝ) (lags : Finset ℕ)
    (α β : ℕ → ℝ) (gp gm : ℝ) (c : Frequency) : ℝ :=
  (∑ n ∈ lags,
    (α n * (G c * (Real.cosh (n*t)-Real.cos (n*Real.arccos c)) -
      2*S c*Real.sin (n*Real.arccos c)) +
     β n * (G c * (Real.cosh (n*t)-Real.cos (n*Real.arccos c)) +
      2*S c*Real.sin (n*Real.arccos c)))) + (gp+gm)*G c

theorem continuous_symbolGS_family {X : Type*} [TopologicalSpace X]
    {G S : X → C(Frequency, ℝ)} {t gp gm : X → ℝ}
    (hG : Continuous G) (hS : Continuous S) (ht : Continuous t)
    (hgp : Continuous gp) (hgm : Continuous gm) (lags : Finset ℕ) (α β : ℕ → ℝ) :
    Continuous (fun q : X × Frequency => symbolGS (G q.1) (S q.1) (t q.1)
      lags α β (gp q.1) (gm q.1) q.2) := by
  have hG' := continuous_eval.comp ((hG.comp continuous_fst).prodMk continuous_snd)
  have hS' := continuous_eval.comp ((hS.comp continuous_fst).prodMk continuous_snd)
  unfold symbolGS
  fun_prop

/-- Uniform g,s perturbations preserve the same lag multipliers and half the margin.
The minimizer multipliers change by exactly the positive and negative charge residuals. -/
theorem StrictCertificate.uniform_gs {a : SymbolPair} {t : ℝ}
    (cert : StrictCertificate a t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a' : SymbolPair) (t' : ℝ),
      |t'-t| ≤ δ → (∀ c, |g a' c-g a c| ≤ δ) →
      (∀ c, |skew a' c-skew a c| ≤ δ) →
      ∃ cert' : StrictCertificate a' t',
        cert'.lags = cert.lags ∧ cert'.α = cert.α ∧ cert'.β = cert.β ∧
        cert'.ε = cert.ε/2 ∧
        cert'.γplus = cert.γplus + max (-(∑ n ∈ cert.lags,
          (cert.α n-cert.β n)*Real.sinh (n*t'))-cert.γplus+cert.γminus) 0 ∧
        cert'.γminus = cert.γminus + max ((∑ n ∈ cert.lags,
          (cert.α n-cert.β n)*Real.sinh (n*t'))+cert.γplus-cert.γminus) 0 := by
  let P := ℝ × (C(Frequency, ℝ) × C(Frequency, ℝ))
  let G₀ : C(Frequency, ℝ) := ⟨g a, continuous_g a⟩
  let S₀ : C(Frequency, ℝ) := ⟨skew a, continuous_skew a⟩
  let x₀ : P := (t, G₀, S₀)
  let q : P → ℝ := fun x => (∑ n ∈ cert.lags,
    (cert.α n-cert.β n)*Real.sinh (n*x.1))+cert.γplus-cert.γminus
  let gp : P → ℝ := fun x => cert.γplus+max (-q x) 0
  let gm : P → ℝ := fun x => cert.γminus+max (q x) 0
  have hq : Continuous q := by dsimp [q, P]; fun_prop
  have hgp : Continuous gp := continuous_const.add (hq.neg.max continuous_const)
  have hgm : Continuous gm := continuous_const.add (hq.max continuous_const)
  have hq₀ : q x₀ = 0 := cert.cancel
  have hgp₀ : gp x₀ = cert.γplus := by simp [gp, hq₀]
  have hgm₀ : gm x₀ = cert.γminus := by simp [gm, hq₀]
  have hs := continuous_symbolGS_family
    (G := fun x : P => x.2.1) (S := fun x : P => x.2.2) (t := fun x : P => x.1)
    continuous_snd.fst continuous_snd.snd continuous_fst hgp hgm cert.lags cert.α cert.β
  have hnear : ∀ᶠ x : P in 𝓝 x₀, ∀ c,
      symbolGS x.2.1 x.2.2 x.1 cert.lags cert.α cert.β (gp x) (gm x) c < -cert.ε/2 := by
    have h := (isCompact_univ : IsCompact (Set.univ : Set Frequency)).eventually_forall_of_forall_eventually
      (P := fun x : P => fun c => symbolGS x.2.1 x.2.2 x.1 cert.lags cert.α cert.β
        (gp x) (gm x) c < -cert.ε/2) (x₀ := x₀) (fun c _ =>
          hs.continuousAt.eventually (gt_mem_nhds (by
            change symbolGS G₀ S₀ t cert.lags cert.α cert.β (gp x₀) (gm x₀) c < -cert.ε/2
            rw [hgp₀, hgm₀]
            change symbol a t cert.lags cert.α cert.β cert.γplus cert.γminus c < -cert.ε/2
            linarith [cert.strict c, cert.ε_pos])))
    simpa only [Set.mem_univ, forall_true_left] using h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ε/2, half_pos hε, fun a' t' htt hgg hss => ?_⟩
  let G' : C(Frequency, ℝ) := ⟨g a', continuous_g a'⟩
  let S' : C(Frequency, ℝ) := ⟨skew a', continuous_skew a'⟩
  let x : P := (t', G', S')
  have hG : dist G' G₀ ≤ ε/2 := by
    rw [dist_eq_norm]
    exact (ContinuousMap.norm_le _ (half_pos hε).le).mpr (fun c => by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, G', G₀, ContinuousMap.coe_mk] using hgg c)
  have hS : dist S' S₀ ≤ ε/2 := by
    rw [dist_eq_norm]
    exact (ContinuousMap.norm_le _ (half_pos hε).le).mpr (fun c => by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, S', S₀, ContinuousMap.coe_mk] using hss c)
  have hdist : dist x x₀ < ε := by
    change max (dist t' t) (max (dist G' G₀) (dist S' S₀)) < ε
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (max_le htt (max_le hG hS)) (by linarith)
  have hx := hball hdist
  have hc : (∑ n ∈ cert.lags, (cert.α n-cert.β n)*Real.sinh (n*t'))+gp x-gm x = 0 := by
    have he : max (-q x) 0-max (q x) 0 = -q x := by
      rcases le_total (q x) 0 with h | h
      · rw [max_eq_left (neg_nonneg.mpr h), max_eq_right h]; ring
      · rw [max_eq_right (neg_nonpos.mpr h), max_eq_left h]; ring
    dsimp [q] at he
    dsimp [gp, gm, x]
    linarith
  refine ⟨{ cert with
    γplus := gp x
    γminus := gm x
    γplus_nonneg := cert.γplus_nonneg.trans (le_add_of_nonneg_right (le_max_right _ _))
    γminus_nonneg := cert.γminus_nonneg.trans (le_add_of_nonneg_right (le_max_right _ _))
    ε := cert.ε/2
    ε_pos := half_pos cert.ε_pos
    cancel := hc
    strict := fun c => by
      change symbolGS G' S' t' cert.lags cert.α cert.β (gp x) (gm x) c ≤ -(cert.ε/2)
      simpa only [neg_div] using (hx c).le },
    rfl, rfl, rfl, rfl, ?_, rfl⟩
  dsimp [gp, q, x]
  congr 2
  ring

/-- At zero exponent the original minimizer multipliers need no adjustment. -/
theorem StrictCertificate.uniform_gs_zero {a : SymbolPair}
    (cert : StrictCertificate a 0) :
    ∃ δ : ℝ,0 < δ ∧ ∀ a' : SymbolPair,
      (∀ c,|g a' c-g a c| ≤ δ) → (∀ c,|skew a' c-skew a c| ≤ δ) →
      ∃ cert' : StrictCertificate a' 0,cert'.lags=cert.lags ∧ cert'.α=cert.α ∧
        cert'.β=cert.β ∧ cert'.ε=cert.ε/2 ∧ cert'.γplus=cert.γplus ∧ cert'.γminus=cert.γminus := by
  obtain ⟨δ,hδ,hnear⟩ := cert.uniform_gs
  refine ⟨δ,hδ,fun a' hg hs => ?_⟩
  obtain ⟨cert',hl,ha,hb,he,hgp,hgm⟩ := hnear a' 0 (by simpa using hδ.le) hg hs
  have hγ : cert.γplus=cert.γminus := sub_eq_zero.mp (by simpa using cert.cancel)
  refine ⟨cert',hl,ha,hb,he,?_,?_⟩
  · simpa [hγ] using hgp
  · simpa [hγ] using hgm

end nesterov.Duality
