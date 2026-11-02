import jacobi.Variational.FredholmSpectrum
import jacobi.Variational.Compactness

/-!
Article: jacobi, Lemma D.1.
The Fredholm observation is continuous along the selected density sequence
when the limiting top eigenvalue is below the pole. At a pole the extended
upper semicontinuity assertion holds because the limiting value is infinity.
Source: local L1 compactness, spectral ordering and uniform truncation estimates.
Use: the quantitative local-to-global argument in Compactness (c).
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter chebyshev2.Continuum
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Convergence of Fredholm observations under a common subcritical margin.
Use: the quantitative local-to-global argument in Compactness (c).
Article: jacobi, Lemma D.1.
Proof: local L1 convergence controls each truncation, and the quadratic spectral
secant bound gives a uniform O(1/R) determinant tail. -/
theorem fredholmReal_limit (m : ℕ → Density) (q : Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) (hqs : SymmetricDecreasing q.value)
    {M E s ε : ℝ} (hM : ∀ n, (m n).mass ≤ M) (hqM : q.mass ≤ M)
    (hE : ∀ n, (m n).energy ≤ E) (hqE : q.energy ≤ E)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x)))
    (hs0 : 0 ≤ s) (hε : 0 < ε)
    (hp : ∀ n, s*observe (m n) .top ≤ 1-ε) (hqp : s*observe q .top ≤ 1-ε) :
    Tendsto (fun n => (m n).fredholmReal s) atTop (𝓝 (q.fredholmReal s)) := by
  -- Both truncations inherit their parent's top-eigenvalue margin by spectral order.
  have htr (p : Density) (R : ℝ) : observe (p.truncate R) .top ≤ observe p .top :=
    (p.truncate R).spectrum_mono p (p.truncate_le R) 0
  apply tendsto_of_uniform_truncations (C := s^2*M^2/(2*ε)) (by positivity)
    (fun R n => ((m n).truncate R).fredholmReal s) (fun R => (q.truncate R).fredholmReal s)
  · exact fun R hR n => (fredholm_truncation_bound (m n) (hs n) hs0 hε (hM n) hR (hp n)).2
  · exact fun R hR => (fredholm_truncation_bound q hqs hs0 hε hqM hR hqp).2
  · intro R _hR
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hl := (local_l1_limit m q hs hqs hE hqE hlim R).const_mul (s/ε)
    simp only [mul_zero] at hl
    apply squeeze_zero (fun _ => norm_nonneg _) _ hl
    intro n
    rw [Real.norm_eq_abs]
    have hb := ((m n).truncate R).fredholmReal_distance (q.truncate R) hs0 hε
      ((mul_le_mul_of_nonneg_left (htr (m n) R) hs0).trans (hp n))
      ((mul_le_mul_of_nonneg_left (htr q R) hs0).trans hqp)
    rwa [truncation_distance] at hb

/-- Subcriticality only at the limit suffices for convergence of the actual determinant.
Use: eliminates the uniform pole-margin hypothesis from Compactness (c).
Article: jacobi, Lemma D.1.
Proof: spectral compactness supplies a uniform margin after finitely many terms;
apply the quantitative theorem to that tail and restore the original sequence. -/
theorem fredholm_limit_of_subcritical (m : ℕ → Density) (q : Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) (hqs : SymmetricDecreasing q.value)
    {M E s : ℝ} (hM : ∀ n, (m n).mass ≤ M) (hqM : q.mass ≤ M)
    (hE : ∀ n, (m n).energy ≤ E) (hqE : q.energy ≤ E)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x)))
    (hs0 : 0 ≤ s) (hqp : s*observe q .top < 1) :
    Tendsto (fun n => (m n).fredholm s) atTop (𝓝 (q.fredholm s)) := by
  -- A fixed half of the limiting pole distance works eventually for every eigenvalue.
  let ε := (1-s*observe q .top)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hqε : s*observe q .top ≤ 1-ε := by dsimp [ε]; linarith
  have ht := (spectral_observation_limit m q hs hqs hM hqM hE hqE hlim .top).const_mul s
  have hev : ∀ᶠ n in atTop, s*observe (m n) .top ≤ 1-ε := by
    apply (ht.eventually (gt_mem_nhds (show s*observe q .top < 1-ε by dsimp [ε]; linarith))).mono
    exact fun n hn => hn.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  have hlim' : ∀ᵐ x, Tendsto (fun n => (m (n+N)).value x) atTop (𝓝 (q.value x)) :=
    hlim.mono (fun x hx => hx.comp (tendsto_add_atTop_nat N))
  have hreal := fredholmReal_limit (fun n => m (n+N)) q (fun n => hs (n+N)) hqs
    (fun n => hM (n+N)) hqM (fun n => hE (n+N)) hqE hlim' hs0 hε
    (fun n => hN (n+N) (Nat.le_add_left N n)) hqε
  have hext := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [← q.fredholm_eq hs0 hε hqε] at hext
  apply (tendsto_add_atTop_iff_nat N).mp
  exact hext.congr (fun n => ((m (n+N)).fredholm_eq hs0 hε
    (hN (n+N) (Nat.le_add_left N n))).symm)

/-- Full extended upper semicontinuity of the Fredholm constraint.
Use: preserves lower Fredholm constraints in the direct method and in Transfer.
Article: jacobi, Lemma D.1.
Proof: below the pole there is actual convergence; at the pole the right side
is genuinely infinite, as proved from its zeroth spectral summand. -/
theorem fredholm_limsup (m : ℕ → Density) (q : Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) (hqs : SymmetricDecreasing q.value)
    {M E s : ℝ} (hM : ∀ n, (m n).mass ≤ M) (hqM : q.mass ≤ M)
    (hE : ∀ n, (m n).energy ≤ E) (hqE : q.energy ≤ E)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x)))
    (hs0 : 0 ≤ s) : limsup (fun n => (m n).fredholm s) atTop ≤ q.fredholm s := by
  -- No pole hypothesis is retained in the final compactness statement.
  by_cases hp : s*observe q .top < 1
  · exact (fredholm_limit_of_subcritical m q hs hqs hM hqM hE hqE hlim hs0 hp).limsup_eq.le
  · have hq : q.fredholm s = ∞ := fredholmSpectrum_eq_top (j := 0) (not_lt.mp hp)
    rw [hq]
    exact le_top

/-- One selected subsequence preserves all moment and Fredholm constraints simultaneously.
Use: the common compactness input for the actual joint moment and Fredholm direct methods.
Article: jacobi, Lemma D.1.
Proof: use the already constructed density subsequence, keep its energy and root-mass
Fatou bounds, and apply the proved Fredholm semicontinuity at every nonnegative parameter. -/
theorem compact_subsequence_with_fredholm (m : ℕ → Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) {M E : ℝ}
    (hM : ∀ n, (m n).mass ≤ M) (hE : ∀ n, (m n).energy ≤ E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : Density,
      SymmetricDecreasing p.value ∧ p.mass ≤ M ∧ p.energy ≤ E ∧
      p.cost ≤ liminf (fun n => (m (φ n)).cost) atTop ∧
      p.rootMass ≤ liminf (fun n => (m (φ n)).rootMass) atTop ∧
      (∀ i, Tendsto (fun n => observe (m (φ n)) i) atTop (𝓝 (observe p i))) ∧
      ∀ s ≥ 0, limsup (fun n => (m (φ n)).fredholm s) atTop ≤ p.fredholm s := by
  -- Selection precedes the Fredholm parameter: the same subsequence works for all s.
  obtain ⟨φ,hφ,p,hps,hpM,hpE,hpoint,hcost,hroot,hspec⟩ := compact_subsequence m hs hM hE
  have hae : ∀ᵐ x, Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (p.value x)) := by
    have hz : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    exact hz.mono hpoint
  exact ⟨φ,hφ,p,hps,hpM,hpE,hcost,hroot,hspec,fun _ hs0 =>
    fredholm_limsup (m ∘ φ) p (fun n => hs (φ n)) hps
      (fun n => hM (φ n)) hpM (fun n => hE (φ n)) hpE hae hs0⟩

end
end jacobi.Variational
