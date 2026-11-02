import jacobi.Variational.Helly
import jacobi.Variational.SpectralLimits

/-!
Article: jacobi, Lemma D.1.
The subsequence and the finite-energy limiting density are constructed here.
The earlier Fatou and spectral continuity results now apply without an assumed
convergent sequence. The logarithmic spatial coordinate keeps the Helly
argument away from the irrelevant singleton zero and allows an unbounded
integrable density near that point.
Use: closes Rearrangement for the article's entire L1 domain before imposing the variational energy bound.
-/
namespace jacobi.Variational
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Mass alone gives a genuine radial L1 subsequential limit; the limiting energy may be infinite.
Use: closes Rearrangement for the article's entire L1 domain before imposing the variational energy bound.
Article: jacobi, Lemma D.1.
Proof: apply the proved Helly theorem in logarithmic coordinates. Fatou
constructs the limiting L1 source using only the uniform mass bound. -/
theorem compact_mass_subsequence (m : ℕ → L1Source)
    (hs : ∀ n,SymmetricDecreasing (m n).value) {M : ℝ}
    (hM : ∀ n,(m n).mass≤M) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧ ∃ q : L1Source,SymmetricDecreasing q.value ∧ q.mass≤M ∧
      ∀ x≠0,Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (q.value x)) := by
  -- In logarithmic coordinates the radial monotonicity is ordinary antitonicity on all of R.
  have hanti (n : ℕ) : Antitone (fun t => (m n).value (exp t)) := by
    intro x y hxy
    exact (hs n).decreasing (exp_pos x) (exp_pos y) (exp_le_exp.mpr hxy)
  have hb (n : ℕ) (r : ℚ) : (m n).value (exp r) ≤ M/(2*exp r) := by
    simpa only [abs_of_pos (exp_pos _)] using
      mass_tail (m n).integrable (m n).nonneg (hs n) (hM n) (exp_pos (r : ℝ)).ne'
  obtain ⟨φ,hφ,g,hg,hg0,hlim⟩ := helly_antitone
    (fun n t => (m n).value (exp t)) hanti (fun n t => (m n).nonneg _)
    (fun r => M/(2*exp r)) hb
  -- Zero can be assigned any finite value; all integrals and all convergence claims avoid it.
  let q (x : ℝ) := if x=0 then 0 else g (log |x|)
  have hqm : Measurable q := Measurable.ite (measurableSet_singleton 0) measurable_const
    (hg.measurable.comp (Real.measurable_log.comp continuous_abs.measurable))
  have hqn (x : ℝ) : 0 ≤ q x := by
    dsimp [q]
    split_ifs <;> first | exact le_rfl | exact hg0 _
  have hqs : SymmetricDecreasing q := by
    constructor
    · intro x
      simp only [q,neg_eq_zero,abs_neg]
    ·
      intro x hx y hy hxy
      change 0 < x at hx
      change 0 < y at hy
      simp only [q,ite_eq_right (ne_of_gt hx),ite_eq_right (ne_of_gt hy),abs_of_pos hx,abs_of_pos hy]
      exact hg (log_le_log hx hxy)
  have hconv (x : ℝ) (hx : x ≠ 0) :
      Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (q x)) := by
    have he (n : ℕ) : (m (φ n)).value (exp (log |x|))=(m (φ n)).value x := by
      rw [exp_log (abs_pos.mpr hx),(hs (φ n)).abs_eq]
    simpa only [he,q,ite_eq_right hx] using hlim (log |x|)
  have hae : ∀ᵐ x,Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (q x)) := by
    have hz : ∀ᵐ x : ℝ,x≠0 := by simp [ae_iff]
    exact hz.mono hconv
  obtain ⟨hi,hbound⟩ := integrable_limit_of_bound
    (fun n => (m (φ n)).integrable) (fun n => (m (φ n)).measurable)
    (fun n => (m (φ n)).nonneg) hqm hqn hae (fun n => hM (φ n))
  exact ⟨φ,hφ,⟨q,hqm,hqn,hi⟩,hqs,hbound,hconv⟩

/-- Full compactness for the mass and energy bounded symmetric decreasing class.
Use: supplies the convergent minimizing subsequence and preserves both spectral
constraints in the direct existence proof and the Transfer theorem.
Article: jacobi, Lemma D.1.
Proof: apply the proved Helly theorem to m_n(exp t), return by log|x|,
construct the actual finite-energy density by Fatou, and apply the verified
local-to-global spectral convergence theorem to this constructed limit. -/
theorem compact_subsequence (m : ℕ → Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) {M E : ℝ}
    (hM : ∀ n, (m n).mass ≤ M) (hE : ∀ n, (m n).energy ≤ E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : Density,
      SymmetricDecreasing p.value ∧ p.mass ≤ M ∧ p.energy ≤ E ∧
      (∀ x ≠ 0, Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (p.value x))) ∧
      p.cost ≤ liminf (fun n => (m (φ n)).cost) atTop ∧
      p.rootMass ≤ liminf (fun n => (m (φ n)).rootMass) atTop ∧
      ∀ i, Tendsto (fun n => observe (m (φ n)) i) atTop (𝓝 (observe p i)) := by
  -- Reuse the mass-only extraction; finite energy is added by the existing Fatou theorem below.
  obtain ⟨φ,hφ,q,hqs,hqM,hconv⟩ := compact_mass_subsequence (fun n => (m n).toL1Source) hs hM
  have hae : ∀ᵐ x,Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (q.value x)) := by
    have hz : ∀ᵐ x : ℝ,x≠0 := by simp [ae_iff]
    exact hz.mono hconv
  -- Finite mass and energy of the selected limit are conclusions of Fatou, not hypotheses.
  obtain ⟨p,hp,hpM,hpE⟩ := finite_energy_limit (m ∘ φ) q.measurable q.nonneg hae
    (fun n => hM (φ n)) (fun n => hE (φ n))
  have hps : SymmetricDecreasing p.value := by rw [hp]; exact hqs
  have hpae : ∀ᵐ x, Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (p.value x)) := by
    simpa only [hp] using hae
  refine ⟨φ,hφ,p,hps,hpM,hpE,?_,energy_liminf (m ∘ φ) p hpae,
    rootMass_liminf (m ∘ φ) p hpae,?_⟩
  · simpa only [hp] using hconv
  · exact spectral_observation_limit (m ∘ φ) p (fun n => hs (φ n)) hps
      (fun n => hM (φ n)) hpM (fun n => hE (φ n)) hpE hpae

end
end jacobi.Variational
