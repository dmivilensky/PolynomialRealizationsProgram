import jacobi.Variational.Compactness

/-!
Article: jacobi, Theorem D.8.
A finite upper bound on the actual extended root mass gives uniform L1 tails.
Combined with the proved local compactness, this yields global L1 convergence
and exact preservation of the total mass. The argument proves an explicit
tail bound instead of assuming a common integrable dominating function.
Use: derives the hypotheses of radial root-tail estimates from the actual variational constraint.
-/
namespace jacobi.Variational
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A finite extended root-mass bound gives the corresponding genuine integrable root.
Use: derives the hypotheses of radial root-tail estimates from the actual variational constraint.
Article: jacobi, Lemma D.1.
Proof: finiteness of the nonnegative lintegral is equivalent to integrability;
the ofReal integral identity then recovers the real upper bound. -/
theorem Density.root_integrable_of_bound (m : Density) {r : ℝ} (hr : 0 ≤ r)
    (hb : m.rootMass ≤ ENNReal.ofReal r) :
    Integrable (fun x => sqrt (m.value x)) ∧ (∫ x, sqrt (m.value x)) ≤ r := by
  -- Keep the extended integral until the absence of a Bochner junk value is proved.
  have hm := Real.continuous_sqrt.measurable.comp m.measurable
  have hi := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => sqrt_nonneg (m.value x))).mp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sqrt_nonneg (m.value x))
  exact ⟨hi,(ENNReal.ofReal_le_ofReal_iff hr).mp (he ▸ hb)⟩

/-- Root-mass bounded radial densities have an explicit uniform L1 truncation error.
Use: the quantitative tightness input for global L1 compactness and exact-mass Transfer.
Article: jacobi, Lemma D.1.
Proof: outside [-R,R], sqrt(m)≤r/(2R), so m≤r sqrt(m)/(2R);
integrate against the proved real root-mass bound. -/
theorem root_truncation_l1 (m : Density) (hs : SymmetricDecreasing m.value)
    {r R : ℝ} (hr : 0 ≤ r) (hb : m.rootMass ≤ ENNReal.ofReal r) (hR : 0 < R) :
    (∫ x, |m.value x-(m.truncate R).value x|) ≤ r^2/(2*R) := by
  -- The removed density is nonnegative, so its absolute integral is its mass.
  obtain ⟨hi,hri⟩ := m.root_integrable_of_bound hr hb
  have hn (x : ℝ) : 0 ≤ m.value x-(m.truncate R).value x := sub_nonneg.mpr (m.truncate_le R x)
  have hpoint (x : ℝ) : m.value x-(m.truncate R).value x ≤ r/(2*R)*sqrt (m.value x) := by
    by_cases hx : x ∈ Icc (-R) R
    · change m.value x-(Icc (-R) R).indicator m.value x ≤ _
      rw [indicator_of_mem hx,sub_self]
      positivity
    · have hrad : R < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
      have hx0 : x ≠ 0 := abs_pos.mp (hR.trans hrad)
      have hroot := (mass_tail hi (fun y => sqrt_nonneg (m.value y)) hs.root hri hx0).trans
        (div_le_div_of_nonneg_left hr (by positivity) (by linarith : 2*R ≤ 2*|x|))
      change m.value x-(Icc (-R) R).indicator m.value x ≤ _
      rw [indicator_of_notMem hx,sub_zero]
      calc
        _ = sqrt (m.value x)*sqrt (m.value x) := by nlinarith [sq_sqrt (m.nonneg x)]
        _ ≤ _ := mul_le_mul_of_nonneg_right hroot (sqrt_nonneg _)
  have h := integral_mono (m.integrable.sub (m.truncate R).integrable)
    (hi.const_mul (r/(2*R))) hpoint
  have he : (∫ x, |m.value x-(m.truncate R).value x|) =
      ∫ x, m.value x-(m.truncate R).value x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => abs_of_nonneg (hn x)
  rw [he]
  calc
    _ ≤ _ := h
    _ = r/(2*R)*(∫ x, sqrt (m.value x)) := integral_const_mul _ _
    _ ≤ r/(2*R)*r := mul_le_mul_of_nonneg_left hri (by positivity)
    _ = _ := by ring

/-- The difference between global and local L1 distance is controlled by the two tails.
Use: applies the scalar uniform-truncation convergence argument to L1 distance itself.
Article: jacobi, Lemma D.1.
Proof: split the full integral into the interval and its complement, and bound
the complementary absolute difference by the sum of the two nonnegative tails. -/
theorem l1_local_distance_bound (m q : Density) {r R : ℝ}
    (hs : SymmetricDecreasing m.value) (hqs : SymmetricDecreasing q.value)
    (hr : 0 ≤ r) (hm : m.rootMass ≤ ENNReal.ofReal r) (hq : q.rootMass ≤ ENNReal.ofReal r)
    (hR : 0 < R) :
    |(∫ x, |m.value x-q.value x|)-(∫ x in Icc (-R) R, |m.value x-q.value x|)| ≤ r^2/R := by
  -- Both local and global distances are integrals of the same integrable nonnegative function.
  have hi := (m.integrable.sub q.integrable).abs
  have hlocal := setIntegral_le_integral (s := Icc (-R) R) hi
    (Filter.Eventually.of_forall fun x => abs_nonneg (m.value x-q.value x))
  have hsplit := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hi
  have ht (x : ℝ) : (Icc (-R) R)ᶜ.indicator (fun x => |m.value x-q.value x|) x ≤
      |m.value x-(m.truncate R).value x|+|q.value x-(q.truncate R).value x| := by
    by_cases hx : x ∈ Icc (-R) R
    · rw [indicator_of_notMem (show x ∉ (Icc (-R) R)ᶜ from by simpa)]
      positivity
    · rw [indicator_of_mem (show x ∈ (Icc (-R) R)ᶜ from hx)]
      simpa only [Density.truncate,indicator_of_notMem hx,sub_zero] using abs_sub (m.value x) (q.value x)
  have h := integral_mono (hi.indicator measurableSet_Icc.compl)
    (((m.integrable.sub (m.truncate R).integrable).abs).add
      ((q.integrable.sub (q.truncate R).integrable).abs)) ht
  rw [integral_indicator measurableSet_Icc.compl] at h
  change (∫ x in (Icc (-R) R)ᶜ, |m.value x-q.value x|) ≤
    ∫ x, |m.value x-(m.truncate R).value x|+|q.value x-(q.truncate R).value x| at h
  have hadd := integral_add (m.integrable.sub (m.truncate R).integrable).abs
    (q.integrable.sub (q.truncate R).integrable).abs
  simp only [Pi.sub_apply] at hadd
  rw [hadd] at h
  change (∫ x in Icc (-R) R, |m.value x-q.value x|) ≤ (∫ x, |m.value x-q.value x|) at hlocal
  rw [abs_of_nonneg (sub_nonneg.mpr hlocal)]
  have hm' := root_truncation_l1 m hs hr hm hR
  have hq' := root_truncation_l1 q hqs hr hq hR
  have he : r^2/(2*R)+r^2/(2*R)=r^2/R := by ring
  change (∫ x in Icc (-R) R, |m.value x-q.value x|)+
    (∫ x in (Icc (-R) R)ᶜ, |m.value x-q.value x|) =
      (∫ x, |m.value x-q.value x|) at hsplit
  linarith

/-- Root-mass bounded radial sequences converge globally in L1 along an a.e. limit.
Use: preserves the equality mass constraint in the root-mass version of Transfer.
Article: jacobi, Lemma D.1.
Proof: Fatou keeps the limit's root mass bounded, local dominated convergence
handles each interval, and the explicit root tails remove the interval uniformly. -/
theorem global_l1_limit (m : ℕ → Density) (q : Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) (hqs : SymmetricDecreasing q.value)
    {E r : ℝ} (hE : ∀ n, (m n).energy ≤ E) (hqE : q.energy ≤ E) (hr : 0 ≤ r)
    (hrb : ∀ n, (m n).rootMass ≤ ENNReal.ofReal r)
    (hlim : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x))) :
    Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0) := by
  -- The finite root-mass condition on the limit follows from the actual extended Fatou inequality.
  have hqr : q.rootMass ≤ ENNReal.ofReal r := (rootMass_liminf m q hlim).trans
    ((liminf_le_liminf (Filter.Eventually.of_forall hrb)).trans_eq (liminf_const _))
  apply tendsto_of_uniform_truncations (C := r^2) (sq_nonneg r)
    (fun R n => ∫ x in Icc (-R) R, |(m n).value x-q.value x|) (fun _ => 0)
  · exact fun R hR n => l1_local_distance_bound (m n) q (hs n) hqs hr (hrb n) hqr hR
  · intro R hR
    simp only [sub_self,abs_zero]
    positivity
  · exact fun R _ => local_l1_limit m q hs hqs hE hqE hlim R

/-- L1 convergence of actual densities implies convergence of their total masses.
Use: retains the exact mass in the stronger root-mass relaxation.
Article: jacobi, Lemma D.1.
Proof: the absolute difference of integrals is bounded by the integral of the absolute difference. -/
theorem mass_limit_of_l1 (m : ℕ → Density) (q : Density)
    (hl : Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0)) :
    Tendsto (fun n => (m n).mass) atTop (𝓝 q.mass) := by
  -- Integrability is stored in each density, so the real integral subtraction is justified.
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hl
  intro n
  have h := norm_integral_le_integral_norm (μ := volume) (fun x => (m n).value x-q.value x)
  rw [integral_sub (m n).integrable q.integrable] at h
  simpa only [Real.norm_eq_abs,Density.mass] using h

/-- The selected compactness subsequence converges globally in L1 when root mass is bounded.
Use: supplies both existence of the limit and exact total-mass convergence in Transfer.
Article: jacobi, Lemma D.1.
Proof: construct the limit using Compactness, obtain its a.e. convergence off
the null singleton zero, apply the proved root-tail argument and then integrate. -/
theorem compact_subsequence_root (m : ℕ → Density)
    (hs : ∀ n, SymmetricDecreasing (m n).value) {M E r : ℝ}
    (hM : ∀ n, (m n).mass ≤ M) (hE : ∀ n, (m n).energy ≤ E)
    (hr : 0 ≤ r) (hrb : ∀ n, (m n).rootMass ≤ ENNReal.ofReal r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : Density,
      SymmetricDecreasing p.value ∧ p.mass ≤ M ∧ p.energy ≤ E ∧
      p.rootMass ≤ ENNReal.ofReal r ∧
      Tendsto (fun n => ∫ x, |(m (φ n)).value x-p.value x|) atTop (𝓝 0) ∧
      Tendsto (fun n => (m (φ n)).mass) atTop (𝓝 p.mass) ∧
      ∀ i, Tendsto (fun n => observe (m (φ n)) i) atTop (𝓝 (observe p i)) := by
  -- Selection, finite energy, root-mass tightness and spectral convergence refer to one common limit.
  obtain ⟨φ,hφ,p,hps,hpM,hpE,hpoint,_,hroot,hspec⟩ := compact_subsequence m hs hM hE
  have hae : ∀ᵐ x, Tendsto (fun n => (m (φ n)).value x) atTop (𝓝 (p.value x)) := by
    have hz : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
    exact hz.mono hpoint
  have hpr : p.rootMass ≤ ENNReal.ofReal r := hroot.trans
    ((liminf_le_liminf (Filter.Eventually.of_forall fun n => hrb (φ n))).trans_eq (liminf_const _))
  have hl := global_l1_limit (m ∘ φ) p (fun n => hs (φ n)) hps
    (fun n => hE (φ n)) hpE hr (fun n => hrb (φ n)) hae
  exact ⟨φ,hφ,p,hps,hpM,hpE,hpr,hl,mass_limit_of_l1 (m ∘ φ) p hl,hspec⟩

end
end jacobi.Variational
