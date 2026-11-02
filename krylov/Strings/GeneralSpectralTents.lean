import krylov.Strings.GeneralSpectralEnergy
import krylov.Strings.SpectralTents
import krylov.Strings.SpectralAtom

/-!
Article: main_krylov, apC:prop:tauber, the physical boundary vector.
Use: exclude spurious spectral mass at infinite energy for arbitrary total
mass by actual shrinking finite-energy tents on one finite-mass prefix.
Source: the concrete piecewise affine tents and continuity of measures from
above. No global finite-mass or density assumption is used.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

variable (S : StringMeasure)

/-- The physical tent radii decrease. -/
theorem tentScale_antitone : Antitone Spectral.tentScale := by
  intro n m hnm
  unfold Spectral.tentScale
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

private theorem tent_memLp (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) (n : ℕ) :
    MemLp (Spectral.tentFunction (n + N)) 2 S.measure := by
  have hi := memLp_indicator_const (μ := S.measure) 2 measurableSet_Icc (1 : ℂ) (Or.inr hf)
  apply hi.of_le
  · exact (Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_id.div_const (Spectral.tentScale (n + N))))).aestronglyMeasurable.indicator
        measurableSet_Icc
  · filter_upwards [] with x
    by_cases hx : x ∈ Icc 0 (Spectral.tentScale N)
    · rw [indicator_of_mem hx, norm_one]
      exact Spectral.tentFunction_norm_le _ _
    · have hn : x ∉ Icc 0 (Spectral.tentScale (n + N)) := by
        intro h
        exact hx ⟨h.1, h.2.trans (tentScale_antitone (Nat.le_add_left N n))⟩
      simp [Spectral.tentFunction, hx, hn]

/-- The actual mass-L² tent, supported in one prescribed finite prefix. -/
def boundaryTent (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) (n : ℕ) : MassHilbert S.measure :=
  (tent_memLp S N hf n).toLp (Spectral.tentFunction (n + N))

/-- The mass-L² tent has its literal piecewise affine representative. -/
theorem boundaryTent_ae (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) (n : ℕ) :
    boundaryTent S N hf n =ᵐ[S.measure] Spectral.tentFunction (n + N) := MemLp.coeFn_toLp _

/-- Equality almost everywhere preserves the actual unit-atom value. -/
theorem eq_at_origin_of_ae_eq {f g : ℝ → ℂ} (h : f =ᵐ[S.measure] g) : f 0 = g 0 := by
  by_contra hn
  have hbad : S.measure {x | f x ≠ g x} = 0 := ae_iff.mp h
  have hsub : ({0} : Set ℝ) ⊆ {x | f x ≠ g x} := by
    intro x hx
    rw [mem_singleton_iff.mp hx]
    exact hn
  have hzero := measure_mono_null hsub hbad
  rw [S.origin] at hzero
  exact one_ne_zero hzero

/-- Every physical tent has actual boundary trace one. -/
theorem boundaryTent_trace (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) (n : ℕ) :
    boundaryTrace S (boundaryTent S N hf n) = 1 := by
  rw [boundaryTrace_apply, eq_at_origin_of_ae_eq S (boundaryTent_ae S N hf n), Spectral.tentFunction_origin]

private theorem finite_shrinking_window (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) (n : ℕ) :
    S.measure (Ioc 0 (Spectral.tentScale (n + N))) ≠ ⊤ :=
  (measure_mono (show Ioc 0 (Spectral.tentScale (n + N)) ⊆ Icc 0 (Spectral.tentScale N) from
    fun _ hx ↦ ⟨hx.1.le, hx.2.trans (tentScale_antitone (Nat.le_add_left N n))⟩)).trans_lt hf.lt_top |>.ne

/-- Shrinking post-origin mass tends to zero on any actual finite prefix. -/
theorem shrinking_window_mass_tendsto (N : ℕ)
    (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ S.measure (Ioc 0 (Spectral.tentScale (n + N)))) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ ↦ Ioc (0 : ℝ) (Spectral.tentScale (n + N))) := by
    intro n m hnm
    exact Ioc_subset_Ioc_right (tentScale_antitone (Nat.add_le_add_right hnm N))
  have hinter : (⋂ n : ℕ, Ioc (0 : ℝ) (Spectral.tentScale (n + N))) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hp := (mem_iInter.mp hx 0).1
    have hlim := Spectral.tentScale_tendsto.comp (tendsto_add_atTop_nat N)
    have he := hlim.eventually (gt_mem_nhds hp)
    obtain ⟨n, hn⟩ := he.exists
    exact (not_lt_of_ge (mem_iInter.mp hx n).2) hn
  have h := tendsto_measure_iInter_atTop (μ := S.measure)
    (fun _ ↦ measurableSet_Ioc.nullMeasurableSet) hanti ⟨0, finite_shrinking_window S N hf 0⟩
  simpa only [hinter, measure_empty, Function.comp_def] using h

private theorem tent_difference_bound (n : ℕ) (x : ℝ) :
    ‖Spectral.tentFunction n x - ({0} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) x‖ ≤
      ‖(Ioc (0 : ℝ) (Spectral.tentScale n)).indicator (fun _ ↦ (1 : ℂ)) x‖ := by
  by_cases hz : x = 0
  · subst x
    simp [Spectral.tentFunction_origin]
  · have hn : x ∉ ({0} : Set ℝ) := by simpa using hz
    rw [indicator_of_notMem hn, sub_zero]
    by_cases hx : x ∈ Ioc 0 (Spectral.tentScale n)
    · rw [indicator_of_mem hx, norm_one]
      exact Spectral.tentFunction_norm_le n x
    · have ho : x ∉ Icc 0 (Spectral.tentScale n) := by
        intro h
        exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hz), h.2⟩
      simp [Spectral.tentFunction, ho, hx]

/-- The actual finite-energy tents converge in global mass L² to the unit
boundary vector, although the total mass may be infinite. -/
theorem boundaryTent_tendsto (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤) :
    Tendsto (boundaryTent S N hf) atTop (𝓝 (boundaryVector S)) := by
  let χ : ℕ → MassHilbert S.measure := fun n ↦
    indicatorConstLp 2 measurableSet_Ioc (finite_shrinking_window S N hf n) (1 : ℂ)
  have hχ : Tendsto χ atTop (𝓝 0) := by
    have h := tendsto_indicatorConstLp_set (μ := S.measure) (p := 2)
      (s := (∅ : Set ℝ)) (hs := MeasurableSet.empty) (hμs := by simp) (c := (1 : ℂ))
      (ht := fun _ : ℕ ↦ measurableSet_Ioc) (hμt := finite_shrinking_window S N hf)
      (by norm_num : (2 : ENNReal) ≠ ⊤) (by
        have he : (fun n : ℕ ↦ S.measure (symmDiff (Ioc 0 (Spectral.tentScale (n + N))) ∅)) =
            (fun n : ℕ ↦ S.measure (Ioc 0 (Spectral.tentScale (n + N)))) := by
          funext n
          congr 1
          ext x
          simp [symmDiff]
        rw [he]
        exact shrinking_window_mass_tendsto S N hf)
    simpa only [indicatorConstLp_empty] using h
  have hb (n : ℕ) : ‖boundaryTent S N hf n - boundaryVector S‖ ≤ ‖χ n‖ := by
    have hh : ‖boundaryTent S N hf n - boundaryVector S‖ ≤ 1 * ‖χ n‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (boundaryTent S N hf n) (boundaryVector S), boundaryTent_ae S N hf n,
        indicatorConstLp_coeFn (μ := S.measure) (s := ({0} : Set ℝ)) (c := (1 : ℂ)),
        indicatorConstLp_coeFn (μ := S.measure) (s := Ioc 0 (Spectral.tentScale (n + N))) (c := (1 : ℂ))]
          with x hsub ht hboundary hi
      simp only [Pi.sub_apply] at hsub
      rw [hsub, ht]
      change ‖Spectral.tentFunction (n + N) x - boundaryVector S x‖ ≤ 1 * ‖χ n x‖
      rw [show boundaryVector S x = ({0} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) x from hboundary,
        show χ n x = (Ioc 0 (Spectral.tentScale (n + N))).indicator (fun _ ↦ (1 : ℂ)) x from hi, one_mul]
      exact tent_difference_bound _ _
    simpa only [one_mul] using hh
  rw [tendsto_iff_dist_tendsto_zero]
  have hn : Tendsto (fun n ↦ ‖χ n‖) atTop (𝓝 (0 : ℝ)) := by simpa using hχ.norm
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ by simpa only [dist_eq_norm] using hb n) hn

/-- Actual tent pairs belong to the true physical derivative graph. -/
theorem boundaryTent_mem_energyGraph (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) (n : ℕ) :
    WithLp.toLp 2 (boundaryTent S N hf n, Spectral.boundaryTentGradient (n + N)) ∈ energyGraph S := by
  apply energyGraph_mem_of_ae
  have hae : ∀ᵐ x ∂S.measure, 0 ≤ x := by
    rw [ae_iff]
    simpa only [not_le, Iio] using hphysical
  filter_upwards [boundaryTent_ae S N hf n, hae] with x ht hx
  rw [ht, boundaryTent_trace]
  exact Spectral.tentFunction_eq_primitive _ hx

/-- No vector in the actual resolvent kernel sees the distinguished
boundary atom; this uses real physical approximating energy functions. -/
theorem neumann_kernel_boundary_inner (N : ℕ) (hf : S.measure (Icc 0 (Spectral.tentScale N)) ≠ ⊤)
    (hphysical : S.measure (Iio 0) = 0) {v : MassHilbert S.measure}
    (hv : neumannResolvent S v = 0) : inner ℂ (boundaryVector S) v = 0 := by
  have ho := (Spectral.compressedProjection_eq_zero_iff (energyGraph S).toSubmodule v).mp hv
  have ht (n : ℕ) : inner ℂ (boundaryTent S N hf n) v = 0 := by
    have hh := ((energyGraph S).toSubmodule.mem_orthogonal _).mp ho _
      (boundaryTent_mem_energyGraph S N hf hphysical n)
    simpa only [Spectral.firstInclusion_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
      WithLp.ofLp_fst, WithLp.ofLp_snd, inner_zero_right, add_zero] using hh
  have hlim : Tendsto (fun n ↦ inner ℂ (boundaryTent S N hf n) v) atTop
      (𝓝 (inner ℂ (boundaryVector S) v)) :=
    (boundaryTent_tendsto S N hf).inner (tendsto_const_nhds (x := v))
  have hz : Tendsto (fun n ↦ inner ℂ (boundaryTent S N hf n) v) atTop (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun n ↦ (ht n).symm)
  exact tendsto_nhds_unique hlim hz

end
end krylov.Strings.GeneralSpectral
