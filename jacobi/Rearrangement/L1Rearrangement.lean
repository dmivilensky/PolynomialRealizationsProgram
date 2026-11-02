import jacobi.Rearrangement.RadialReduction

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
The original source may have infinite energy and infinite root mass.
Regular L1 approximation and the proved regular rearrangement give a radial
mass-bounded family. Mass-only Helly extraction and continuous distribution
tests identify an equimeasurable L1 limit. Layer cake preserves every positive
power integral, including infinity; Scheffe then transfers every actual
spectral moment. The full extended Fredholm series retains its pole values.
Source: Helly selection, Cavalieri's formula and Scheffe's lemma, proved in the imported modules.
Use: closes the domain difference between the source's Rearrangement lemma and the finite-energy variational specialization.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter jacobi.Variational
open chebyshev2.Continuum
open scoped ENNReal Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- Every nonnegative L1 source has the full equimeasurable spectral rearrangement, even when its energy is infinite.
Use: closes the domain difference between the source's Rearrangement lemma and the finite-energy variational specialization.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: rearrange regular L1 approximants, extract a radial limit using only
mass, and identify all its positive superlevels by continuous clipped tests.
Layer cake gives every power normalization. Exact mass upgrades the radial
convergence to L1; spectral stability passes all moments and the Fredholm series to the limit. -/
theorem exists_l1_rearrangement (m : L1Source) :
    ∃ q : L1Source,SymmetricDecreasing q.value ∧ q.mass=m.mass ∧
      (∀ t,volume {x | t<q.value x}=volume {x | t<m.value x}) ∧
      (∀ p : ℝ,0<p → (∫⁻ x,ENNReal.ofReal (q.value x^p))=∫⁻ x,ENNReal.ofReal (m.value x^p)) ∧
      (∀ n : ℕ,(∑' j,m.spectrum j^(n+1))≤∑' j,q.spectrum j^(n+1)) ∧
      observe m .top≤observe q .top ∧
      ∀ s : ℝ,0≤s → m.fredholm s≤q.fredholm s := by
  -- Approximation and extraction require finite mass only; no uniform energy bound is introduced.
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0<ε n := by dsimp only [ε]; positivity
  have hε1 (n : ℕ) : ε n≤1 := by
    change 1/((n:ℝ)+1)≤1
    exact div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f R C K hR hf herr using fun n => exists_regular_l1_approx m.integrable m.nonneg (hε n)
  choose g hgr hs hdist hmass henergy hroot hmoment htop hfred htests using
    fun n => regular_rearrangement (hR n) (hf n)
  let a (n : ℕ) := regularDensity (f n) (hf n)
  let b (n : ℕ) := regularDensity (g n) (hgr n)
  have hma (n : ℕ) : |(a n).mass-m.mass|≤ε n := by
    rw [abs_sub_comm]
    exact (integral_distance m.integrable (a n).integrable).trans (herr n)
  have hM (n : ℕ) : (a n).mass≤m.mass+1 := by
    have hh := (abs_le.mp (hma n)).2
    linarith [hε1 n]
  have hMB (n : ℕ) : (b n).mass≤m.mass+1 := (hmass n).le.trans (hM n)
  have ham : Tendsto (fun n => (a n).mass) atTop (𝓝 m.mass) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hma) hεlim
  have hbm : Tendsto (fun n => (b n).mass) atTop (𝓝 m.mass) := ham.congr fun n => (hmass n).symm
  obtain ⟨φ,hφ,q,hqs,hqM,hpoint⟩ := compact_mass_subsequence
    (fun n => (b n).toL1Source) hs hMB
  have hpae : ∀ᵐ x,Tendsto (fun n => (b (φ n)).value x) atTop (𝓝 (q.value x)) := by
    have hz : ∀ᵐ x : ℝ,x≠0 := by simp [ae_iff]
    exact hz.mono hpoint
  have hL1 : Tendsto (fun n => ∫ x,|(a n).value x-m.value x|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _ hεlim
    intro n
    change (∫ x,|f n x-m.value x|)≤ε n
    simpa only [abs_sub_comm] using herr n
  -- Continuous tests identify the distribution before using exact mass to assert tightness.
  have hTests (t : ℝ) (ht : 0<t) (δ : ℝ) (hδ : 0<δ) :
      (∫ x,softTest t δ (q.value x))=∫ x,softTest t δ (m.value x) := by
    have ha := softTest_integral_limit_l1 a m hL1 ht.le hδ.le
    have hb := softTest_integral_limit_radial (b ∘ φ) q (fun n => hs (φ n))
      (fun n => hMB (φ n)) hpae ht hδ.le
    have he (n : ℕ) : (∫ x,softTest t δ ((b (φ n)).value x))=
        ∫ x,softTest t δ ((a (φ n)).value x) :=
      htests (φ n) (softTest t δ) (softTest_lipschitz t δ).continuous (softTest_zero hδ.le ht.le)
    exact tendsto_nhds_unique hb ((ha.comp hφ.tendsto_atTop).congr fun n => (he n).symm)
  have hlevels := fun t ht => superlevel_eq_of_softTests m q hTests (t := t) ht
  have hmassEq : q.mass=m.mass := by
    have hh := power_integral_eq_of_superlevels m q hlevels (p := 1) zero_lt_one
    simp only [Real.rpow_one] at hh
    rw [← ofReal_integral_eq_lintegral_ofReal q.integrable (Eventually.of_forall q.nonneg),
      ← ofReal_integral_eq_lintegral_ofReal m.integrable (Eventually.of_forall m.nonneg)] at hh
    have he := congrArg ENNReal.toReal hh
    simpa only [L1Source.mass,ENNReal.toReal_ofReal (integral_nonneg q.nonneg),
      ENNReal.toReal_ofReal (integral_nonneg m.nonneg)] using he
  have hbmq : Tendsto (fun n => (b (φ n)).mass) atTop (𝓝 q.mass) := by
    rw [hmassEq]
    exact hbm.comp hφ.tendsto_atTop
  have hbL1 := l1_limit_of_ae_mass_limit (b ∘ φ) q hpae hbmq
  have hAll (n : ℕ) : (∑' j,m.spectrum j^(n+1))≤∑' j,q.spectrum j^(n+1) := by
    have ha := moment_limit_of_l1 a m hM (le_add_of_nonneg_right zero_le_one) hL1 n
    have hb := moment_limit_of_l1 (b ∘ φ) q (fun n => hMB (φ n)) hqM hbL1 n
    exact le_of_tendsto_of_tendsto (ha.comp hφ.tendsto_atTop) hb
      (Eventually.of_forall fun k => hmoment (φ k) n)
  have hTop : observe m .top≤observe q .top := by
    apply le_of_tendsto_of_tendsto (jacobi.Continuum.kernel_moment_root_limit m.integrable m.nonneg)
      (jacobi.Continuum.kernel_moment_root_limit q.integrable q.nonneg)
    exact Eventually.of_forall fun n => Real.rpow_le_rpow
      (tsum_nonneg fun j => pow_nonneg ((kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg j) _)
      (hAll n) (by positivity)
  exact ⟨q,hqs,hmassEq,all_superlevels_eq_of_positive m q hlevels,
    fun p hp => power_integral_eq_of_superlevels m q hlevels hp,hAll,hTop,
    fun s hs => fredholm_mono_of_moments m q hs (fun n => by simpa only [Nat.add_assoc] using hAll (n+1))⟩

end
end jacobi.Rearrangement
