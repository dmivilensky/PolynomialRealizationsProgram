import jacobi.Rearrangement.EnergyApproximation
import jacobi.Variational.Tightness
import jacobi.Variational.FredholmCompactness
import jacobi.Variational.FredholmLowerSemicontinuity
import jacobi.Rearrangement.DistributionTests
import jacobi.Variational.MomentStability

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Every actual finite-energy density has an equimeasurable symmetric decreasing
rearrangement preserving mass, energy and root mass exactly and increasing all
positive integer spectral moments, the top eigenvalue and all extended
Fredholm observations, including poles.
The proof applies the complete regular rearrangement theorem to proved
finite-energy approximations, then uses the already constructed radial
compactness subsequence. Clipped value tests identify the general limit's
distribution without assuming tightness; layer cake recovers exact integral
identities and Scheffe then supplies global L1 convergence for every moment.
Source: regular rearrangement, Fatou and the direct method of the calculus of variations.
Use: preserves exact mass and root normalization in Transfer and removes symmetry from both direct methods.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter jacobi.Variational
open scoped NNReal ENNReal Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- Every finite-energy density has an actual equimeasurable symmetric decreasing rearrangement with all spectral improvements.
Use: preserves exact mass and root normalization in Transfer and removes symmetry from both direct methods.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: rearrange proved regular approximants. Their mass and energy converge
to the original values, while L1 spectral stability controls both observations.
The proved radial compactness theorem produces an actual density; Fatou gives
the initial upper mass and energy bounds. Continuous clipped tests identify
the complete limiting distribution; layer cake recovers all exact normalizations.
Scheffe and spectral stability preserve every cyclic moment, while lower and
upper Fredholm semicontinuity preserve all parameters, including spectral poles. -/
theorem exists_equimeasurable_rearrangement (m : Density) :
    ∃ q : Density, SymmetricDecreasing q.value ∧ q.mass=m.mass ∧ q.energy=m.energy ∧
      q.rootMass=m.rootMass ∧ (∀ t, volume {x | t < q.value x}=volume {x | t < m.value x}) ∧
      (∀ i : Observation, observe m i ≤ observe q i) ∧
      (∀ s : ℝ, 0 ≤ s → m.fredholm s ≤ q.fredholm s) ∧
      ∀ p : ℕ, (∑' j, m.spectrum j^(p+1)) ≤ ∑' j, q.spectrum j^(p+1) := by
  -- Approximate the literal original density in both L1 and the absolute energy-integrand distance.
  let ε (n : ℕ) : ℝ := 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    change 1/((n : ℝ)+1) ≤ 1
    exact div_le_self (by norm_num : (0 : ℝ) ≤ 1)
      (le_add_of_nonneg_left (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f R C K hR hf h1 hE using fun n => exists_regular_finite_energy_approx m (hε n)
  choose g hgr hshape hdist hmass henergy hroot hmoment htop hfred htests using
    fun n => regular_rearrangement (hR n) (hf n)
  let a (n : ℕ) := regularDensity (f n) (hf n)
  let b (n : ℕ) := regularDensity (g n) (hgr n)
  have hma (n : ℕ) : |(a n).mass-m.mass| ≤ ε n := by
    rw [abs_sub_comm]
    exact (integral_distance m.integrable (a n).integrable).trans (h1 n)
  have hea (n : ℕ) : |(a n).energy-m.energy| ≤ ε n := by
    rw [abs_sub_comm]
    exact (integral_distance m.energy_integrable (a n).energy_integrable).trans (hE n)
  have hM (n : ℕ) : (a n).mass ≤ m.mass+1 := by
    have h := (abs_le.mp (hma n)).2
    linarith [hε1 n]
  have hEB (n : ℕ) : (b n).energy ≤ m.energy+1 := by
    change (regularDensity (g n) (hgr n)).energy ≤ _
    rw [henergy n]
    have h := (abs_le.mp (hea n)).2
    linarith [hε1 n]
  have hMB (n : ℕ) : (b n).mass ≤ m.mass+1 := by
    change (regularDensity (g n) (hgr n)).mass ≤ _
    rw [hmass n]
    exact hM n
  have ham : Tendsto (fun n => (a n).mass) atTop (𝓝 m.mass) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hma) hεlim
  have hae : Tendsto (fun n => (a n).energy) atTop (𝓝 m.energy) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hea) hεlim
  have hbm : Tendsto (fun n => (b n).mass) atTop (𝓝 m.mass) := by
    exact ham.congr (fun n => (hmass n).symm)
  have hbe : Tendsto (fun n => (b n).cost) atTop (𝓝 m.cost) := by
    have ht := hae.congr (fun n => (henergy n).symm)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  -- Compactness selects the density and the subsequence, so no convergence premise survives in the conclusion.
  obtain ⟨φ,hφ,q,hqs,hqM,hqE,hpoint,hcost,hr,hobs⟩ :=
    compact_subsequence b hshape hMB hEB
  have hpae : ∀ᵐ x, Tendsto (fun n => (b (φ n)).value x) atTop (𝓝 (q.value x)) := by
    have hz : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    exact hz.mono hpoint
  have hqm : q.mass ≤ m.mass := by
    have h := mass_liminf (b ∘ φ) q hpae
    have ht := ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbm).comp hφ.tendsto_atTop).liminf_eq
    simp only [Function.comp_def] at ht h
    rw [ht] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg m.nonneg)).mp h
  have hqe : q.energy ≤ m.energy := by
    have ht := (hbe.comp hφ.tendsto_atTop).liminf_eq
    simp only [Function.comp_def] at ht
    rw [ht] at hcost
    exact (ENNReal.ofReal_le_ofReal_iff m.energy_nonneg).mp hcost
  have hmo (i : Observation) : observe m i ≤ observe q i := by
    -- Both original observations converge along the approximating sequence by the same actual L1 spectral bound.
    have hao : Tendsto (fun n => observe (a n) i) atTop (𝓝 (observe m i)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      cases i with
      | top =>
        apply squeeze_zero (fun _ => norm_nonneg _) _ hεlim
        intro n
        rw [Real.norm_eq_abs,abs_sub_comm]
        exact (kernel_top_distance m.integrable (a n).integrable m.nonneg (a n).nonneg).trans (h1 n)
      | second =>
        have ht := hεlim.const_mul (2*m.mass+1)
        rw [mul_zero] at ht
        apply squeeze_zero (fun _ => norm_nonneg _) _ ht
        intro n
        rw [Real.norm_eq_abs,abs_sub_comm]
        have hb := kernel_square_distance m.integrable (a n).integrable m.nonneg (a n).nonneg
        change |observe m .second-observe (a n) .second| ≤
          (m.mass+(a n).mass)*(∫ x, |m.value x-(a n).value x|) at hb
        apply hb.trans
        have hm0 : 0 ≤ m.mass := integral_nonneg m.nonneg
        exact mul_le_mul (by linarith [hM n]) (h1 n)
          (integral_nonneg (fun _ => abs_nonneg _)) (by linarith)
    apply le_of_tendsto_of_tendsto (hao.comp hφ.tendsto_atTop) (hobs i)
    exact Eventually.of_forall fun n => by
      cases i with
      | top => exact htop (φ n)
      | second => simpa only [observe,L1Source.spectrum,Function.comp_def,Nat.reduceAdd] using hmoment (φ n) 1
  have hL1 : Tendsto (fun n => ∫ x, |(a n).value x-m.value x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hεlim
    intro n
    change (∫ x, |f n x-m.value x|) ≤ ε n
    simpa only [abs_sub_comm] using h1 n
  -- Continuous tests away from value zero identify the limiting distribution before asserting exact mass.
  have hTests (t : ℝ) (ht : 0 < t) (δ : ℝ) (hδ : 0 < δ) :
      (∫ x, softTest t δ (q.value x))=∫ x, softTest t δ (m.value x) := by
    have ha := softTest_integral_limit_l1 a m hL1 ht.le hδ.le
    have hb := softTest_integral_limit_radial (b ∘ φ) q
      (fun n => hshape (φ n)) (fun n => hMB (φ n)) hpae ht hδ.le
    have he (n : ℕ) : (∫ x, softTest t δ ((b (φ n)).value x))=
        ∫ x, softTest t δ ((a (φ n)).value x) :=
      htests (φ n) (softTest t δ) (softTest_lipschitz t δ).continuous
        (softTest_zero hδ.le ht.le)
    exact tendsto_nhds_unique hb ((ha.comp hφ.tendsto_atTop).congr (fun n => (he n).symm))
  have hpositive := fun t ht => superlevel_eq_of_softTests m q hTests (t := t) ht
  obtain ⟨hmassExact,henergyExact,hrootExact⟩ := integrals_eq_of_superlevels m q hpositive
  -- Exact distribution gives exact mass, and Scheffe then upgrades radial convergence to global L1 convergence.
  have hbmq : Tendsto (fun n => (b (φ n)).mass) atTop (𝓝 q.mass) := by
    rw [hmassExact]
    exact hbm.comp hφ.tendsto_atTop
  have hbL1 := l1_limit_of_ae_mass_limit (b ∘ φ) q hpae hbmq
  have hAll (p : ℕ) : (∑' j, m.spectrum j^(p+1)) ≤ ∑' j, q.spectrum j^(p+1) := by
    have hmM : m.mass ≤ m.mass+1 := le_add_of_nonneg_right (by norm_num)
    have ha := moment_limit_of_l1 a m hM hmM hL1 p
    have hb := moment_limit_of_l1 (b ∘ φ) q (fun n => hMB (φ n)) hqM hbL1 p
    apply le_of_tendsto_of_tendsto (ha.comp hφ.tendsto_atTop) hb
    exact Eventually.of_forall fun n => hmoment (φ n) p
  have hFr (s : ℝ) (hs : 0 ≤ s) : m.fredholm s ≤ q.fredholm s := by
    -- Scalar and spectral Fatou also cover poles, so regular approximation needs no pole margin.
    have hl := fredholm_le_liminf_of_l1 (a ∘ φ) m (hL1.comp hφ.tendsto_atTop) hs
    have hm := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n => hfred (φ n) s hs)
    have hu := fredholm_limsup (b ∘ φ) q (fun n => hshape (φ n)) hqs
      (fun n => hMB (φ n)) hqM (fun n => hEB (φ n)) hqE hpae hs
    exact hl.trans (hm.trans (le_trans liminf_le_limsup hu))
  exact ⟨q,hqs,hmassExact,henergyExact,hrootExact,all_superlevels_eq_of_positive m q hpositive,hmo,hFr,hAll⟩

/-- Every finite-energy density has a radial replacement improving both moment constraints and all Fredholm observations.
Use: the root-free projection of the stronger equimeasurable rearrangement used by both direct methods.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the proved equimeasurable density preserves mass and energy exactly,
so in particular meets their upper bounds while keeping all spectral improvements. -/
theorem exists_radial_replacement (m : Density) :
    ∃ q : Density, SymmetricDecreasing q.value ∧ q.mass ≤ m.mass ∧ q.energy ≤ m.energy ∧
      (∀ i : Observation, observe m i ≤ observe q i) ∧
      ∀ s : ℝ, 0 ≤ s → m.fredholm s ≤ q.fredholm s := by
  obtain ⟨q,hs,hM,hE,_,_,hO,hF,_⟩ := exists_equimeasurable_rearrangement m
  exact ⟨q,hs,hM.le,hE.le,hO,hF⟩

/-- Every finite-energy density has a radial replacement improving both moment constraints.
Use: the moment-only projection of the common radial reduction for the root-free direct method.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: specialize the proved common moment and Fredholm radial replacement theorem. -/
theorem exists_radial_moment_replacement (m : Density) :
    ∃ q : Density, SymmetricDecreasing q.value ∧ q.mass ≤ m.mass ∧ q.energy ≤ m.energy ∧
      ∀ i : Observation, observe m i ≤ observe q i := by
  obtain ⟨q,hs,hM,hE,hO,_⟩ := exists_radial_replacement m
  exact ⟨q,hs,hM,hE,hO⟩

end
end jacobi.Rearrangement
