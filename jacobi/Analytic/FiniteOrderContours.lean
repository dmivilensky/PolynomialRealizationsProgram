import jacobi.Analytic.BesselOrderContinuity
import jacobi.Bessel.EdgeData
import Mathlib.Topology.Compactness.Compact

/-!
Article: jacobi, Lemma E.1.
Every fixed compact zero-free spectral contour has a common complex
order neighborhood with a positive lower bound for the actual Bessel
function. Explicit circles between consecutive original squared zeros
provide such contours without an additional zero-exclusion assumption.
This finite-prefix result does not assert a neighborhood uniform over
the entire infinite zero sequence; that requires the Hankel estimates.
Use: finite_order_contour_bound discharges this compact-contour condition for the genuine original spectral prefix in the proof of zero continuation.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter Metric
open scoped Topology

/-- A compact zero-free contour retains a positive actual Bessel lower bound on one common complex-order neighborhood.
Use: finite_order_contour_bound discharges this compact-contour condition for the genuine original spectral prefix in the proof of zero continuation.
Article: jacobi, Lemma E.1.
Source: the compact tube lemma and the proved joint continuity of the actual normalized Bessel series.
Proof: minimize the nonzero original Bessel norm on the compact contour.
Half its positive minimum defines an open joint order/spectral set.
The compact tube lemma supplies one order neighborhood that works for
every point of the original contour simultaneously. -/
theorem compact_order_contour_bound {a:ℂ} (ha:-1<a.re)
    {K:Set ℂ} (hK:IsCompact K) (hz:∀z∈K,normalized a z≠0) :
    ∃ r c:ℝ,0<r ∧ 0<c ∧ ∀b∈ball a r,
      -1<b.re ∧ ∀z∈K,c≤‖normalized b z‖ := by
  -- Compactness produces a single genuine parameter neighborhood, not a separate radius for each contour point.
  by_cases hne:K.Nonempty
  · obtain ⟨z,hzK,hmin⟩ := hK.exists_isMinOn hne
      (fun w _ => (normalized_analytic a w).continuousAt.norm.continuousWithinAt)
    let c : ℝ := ‖normalized a z‖/2
    have hc : 0<c := half_pos (norm_pos_iff.mpr (hz z hzK))
    let O : Set (ℂ × ℂ) := {p | -1<p.1.re ∧ c<‖normalized p.1 p.2‖}
    have hO : IsOpen O := normalized_order_spectral_continuous.norm.isOpen_inter_preimage
      (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)) isOpen_Ioi
    have hin : ({a}:Set ℂ) ×ˢ K⊆O := by
      rintro ⟨b,w⟩ ⟨hb,hw⟩
      have hb' : b=a := hb
      subst b
      refine ⟨ha,?_⟩
      have hm := hmin hw
      change ‖normalized a z‖≤‖normalized a w‖ at hm
      dsimp only [c]
      linarith [norm_pos_iff.mpr (hz z hzK)]
    obtain ⟨U,V,hU,_hV,haU,hKV,hUV⟩ :=
      generalized_tube_lemma isCompact_singleton hK hO hin
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (haU (mem_singleton a)))
    refine ⟨r,c,hr,hc,fun b hb=>?_⟩
    have hbU := hrU hb
    refine ⟨?_,fun w hw=>
      (hUV (show (b,w)∈U ×ˢ V from ⟨hbU,hKV hw⟩)).2.le⟩
    exact (hUV (show (b,z)∈U ×ˢ V from ⟨hbU,hKV hzK⟩)).1
  · have hK0 : K=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (order_halfPlane_open.mem_nhds ha)
    exact ⟨r,1,hr,by norm_num,fun b hb=>⟨hrU hb,by simp only [hK0,Set.mem_empty_iff_false,forall_false,implies_true]⟩⟩

/-- The explicit original circle midway between consecutive squared Bessel zeros excludes every actual complex spectral zero.
Use: finite_order_contour_bound applies compact parameter stability to a fully verified actual original spectral contour.
Article: jacobi, Lemma E.1.
Proof: every original complex zero is positive real and occurs in the
proved exhaustive increasing sigma list. Its modulus therefore lies
either below the smaller neighbor or above the larger one, never at
their strictly intermediate radius. -/
theorem finite_contour_nonzero (a:ℝ) (ha:-1<a) (k:ℕ) {z:ℂ}
    (hz:z∈sphere 0 ((sigma a ha k+sigma a ha (k+1))/2)) :
    normalized (a:ℂ) z≠0 := by
  -- Zero location and enumeration both concern the unchanged original entire Bessel function.
  intro hzero
  obtain ⟨x,hx,he⟩ := normalized_zero_positive ha hzero
  have hxzero : (x:ℂ)=z := he.symm
  have hxspec : x∈spectralZeros a := by
    change normalized (a:ℂ) (x:ℂ)=0
    rw [hxzero]
    exact hzero
  obtain ⟨l,hl⟩ := sigma_exhaustive ha hxspec
  have hnorm : ‖z‖=(sigma a ha k+sigma a ha (k+1))/2 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using hz
  rw [← hxzero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,← hl] at hnorm
  have hgap := sigma_strictMono ha (Nat.lt_succ_self k)
  rcases le_or_gt l k with h | h
  · have hm := (sigma_strictMono ha).monotone h
    linarith
  · have hm := (sigma_strictMono ha).monotone (show k+1≤l by omega)
    linarith

/-- Every actual finite-prefix spectral circle has a positive Bessel lower bound uniform over a genuine complex-order disk.
Use: supplies the fully discharged finite-prefix contour part of, 's zero continuation before the independent all-index complex Hankel tail is combined with it.
Article: jacobi, Lemma E.1.
Proof: the actual circle is compact and the complete original zero
classification excludes zeros on it. The proved joint compact-contour
stability theorem gives the same order radius for every contour point. -/
theorem finite_order_contour_bound (a:ℝ) (ha:-1<a) (k:ℕ) :
    ∃ r c:ℝ,0<r ∧ 0<c ∧ ∀b∈ball (a:ℂ) r,
      -1<b.re ∧ ∀z∈sphere (0:ℂ) ((sigma a ha k+sigma a ha (k+1))/2),
        c≤‖normalized b z‖ :=
  compact_order_contour_bound (by simpa only [Complex.ofReal_re] using ha)
    (isCompact_sphere _ _) (fun _ hz=>finite_contour_nonzero a ha k hz)

end
end jacobi.Bessel
