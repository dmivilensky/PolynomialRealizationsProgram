import nesterov.Attainment.FinitePolynomial

/-! The article's atom-count theorem: the largest active lag of any one
optimizer bounds a single finite carrier shared by every optimal spectrum. -/
noncomputable section
open MeasureTheory Set
namespace nesterov.Attainment
open Spectral

theorem optimal_activeLags_finite (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    (activeLags M μ L (Closure.T M μ L) ν C).Finite := by
  obtain ⟨N,hN⟩ := optimal_active_lags_bounded M hμ hμL ht htq h
  apply (Set.finite_Icc 1 N).subset
  intro n hn
  refine ⟨hn.1, ?_⟩
  by_contra hnot
  have hp := hN n (by omega)
  rcases hn.2 with hl | hu
  · exact (ne_of_gt hp.1) hl
  · exact (ne_of_gt hp.2) hu

theorem optimal_activeLags_nonempty (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    (activeLags M μ L (Closure.T M μ L) ν C).Nonempty := by
  obtain ⟨B⟩ := exists_boundaryDual M hμ hμL ht
  by_contra hnone
  have hN : ∀ n∈activeLags M μ L (Closure.T M μ L) ν C,n ≤ 0 := by
    intro n hn
    exact False.elim (hnone ⟨n,hn⟩)
  have hm := B.measure_finite_lags h (optimal_strict_minimizer M hμ hμL ht htq h) hN
  have he : finiteLagLabels 0=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro l ⟨⟨b,n⟩,_⟩
    exact Fin.elim0 n
  simp only [he,Set.compl_empty,measure_univ,one_ne_zero] at hm

theorem optimal_activeLags_has_maximum (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    ∃ N, IsGreatest (activeLags M μ L (Closure.T M μ L) ν C) N :=
  (optimal_activeLags_finite M hμ hμL ht htq h).isCompact.exists_isGreatest
    (optimal_activeLags_nonempty M hμ hμL ht htq h)

/-- Lemma count, in the stronger form that any upper bound on one optimizer's
active lags gives the same sharp bound for every optimal probability spectrum. -/
theorem optimal_common_carrier_atom_count (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C)
    (N : ℕ) (hN : ∀ n∈activeLags M μ L (Closure.T M μ L) ν C,n ≤ N) :
    ∃ F : Set Frequency,F.Finite ∧ F.ncard ≤ (M.memory+N)/2 ∧
      (∀ c∈F,-1 < (c:ℝ) ∧ (c:ℝ) < 1) ∧
      ∀ (ν' : Spectrum) (C' : ℝ),Feasible (M.symbolPair μ L (Closure.T M μ L))
        (Closure.T M μ L) ν' C' → (ν' : Measure Frequency) Fᶜ=0 := by
  obtain ⟨B⟩ := exists_boundaryDual M hμ hμL ht
  obtain ⟨E⟩ := B.exists_finite_expansion h (optimal_strict_minimizer M hμ hμL ht htq h) hN
  exact ⟨B.zeroSet,B.zeroSet_finite hμ hμL htq,E.atom_count hμ hμL htq,
    fun _ hc => B.zeroSet_interior hμ hμL htq hc,fun _ _ h' => B.measure_carried h'⟩

/-- In particular the bound uses exactly the largest active lag of any fixed
optimal pair, as stated in the article. -/
theorem atom_count_of_largest_active (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C)
    {N : ℕ} (hN : IsGreatest (activeLags M μ L (Closure.T M μ L) ν C) N) :
    ∃ F : Set Frequency,F.Finite ∧ F.ncard ≤ (M.memory+N)/2 ∧
      (∀ c∈F,-1 < (c:ℝ) ∧ (c:ℝ) < 1) ∧
      ∀ (ν' : Spectrum) (C' : ℝ),Feasible (M.symbolPair μ L (Closure.T M μ L))
        (Closure.T M μ L) ν' C' → (ν' : Measure Frequency) Fᶜ=0 :=
  optimal_common_carrier_atom_count M hμ hμL ht htq h N (fun _ hn => hN.2 hn)

/-- A fixed genuine real Euclidean objective attains T in dimension 2J,
with J bounded by half the memory plus the chosen optimizer's largest active lag. -/
theorem optimal_real_attainment_with_atom_count (M : StationaryMethod) {μ L C : ℝ} {ν : Spectrum}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C)
    {N : ℕ} (hN : IsGreatest (activeLags M μ L (Closure.T M μ L) ν C) N) :
    ∃ J : ℕ,J ≤ (M.memory+N)/2 ∧
      ∃ (f : EuclideanSpace ℝ (Fin (2*J)) → ℝ) (w : ℕ → EuclideanSpace ℝ (Fin (2*J))),
        polyak.CenteredSmoothStronglyConvex μ L f ∧ M.IsTrajectory (gradient f) w ∧
          ∀ k, ‖w k‖=Real.exp (k*Closure.T M μ L) := by
  classical
  obtain ⟨F,hF,hcard,_,hcarrier⟩ := atom_count_of_largest_active M hμ hμL ht htq h hN
  let : Fintype F := hF.fintype
  obtain ⟨weights,hw,he⟩ := polyak.Spectral.exists_finiteSpectrum_of_support ν (hcarrier ν C h)
  rw [← he] at h
  obtain ⟨f,w,hf,htj,hnorm⟩ := finite_exists_real_objective M hμ hμL weights (fun j => j.val) hw h
  refine ⟨Fintype.card F,?_,f,w,hf,htj,hnorm⟩
  have hcf : Fintype.card F=F.ncard := Set.fintypeCard_eq_ncard F
  rwa [hcf]

end nesterov.Attainment
