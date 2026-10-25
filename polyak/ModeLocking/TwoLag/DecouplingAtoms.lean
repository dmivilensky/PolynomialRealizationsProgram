import polyak.ModeLocking.TwoLag.DecouplingCertificate
import polyak.Farey.FanDivergence.TwoLag

/-! The complete closed mass-ratio interval for two actual atoms, with
the minimizer slack kept explicit. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Levels MeasureTheory Set

def pairMeasure (u v : Frequency) (r : NNReal) : Measure Frequency :=
  atomicMeasure (![1,r] : Fin 2→NNReal) (![u,v] : Fin 2→Frequency)

instance finite_pairMeasure (u v : Frequency) (r : NNReal) : IsFiniteMeasure (pairMeasure u v r) :=
  inferInstanceAs (IsFiniteMeasure (atomicMeasure _ _))

theorem pairMeasure_integral (u v : Frequency) (r : NNReal) (f : Frequency→ℝ) :
    (∫ω,f ω∂pairMeasure u v r)=f u+(r : ℝ)*f v := by
  rw [pairMeasure,atomicMeasure_integral,Fin.sum_univ_two]
  norm_num

theorem pairMeasure_literal (u v : Frequency) (r : NNReal) :
    pairMeasure u v r=Measure.dirac u+(r : ENNReal)•Measure.dirac v := by
  simp [pairMeasure,atomicMeasure,Fin.sum_univ_two]

theorem pair_ratio_constraints_iff {Θ : Curve} {K : ℕ} {u v : Frequency}
    (hv : v∈minusSet Θ K) (r : ℝ) :
    (0≤Θ.lag 1 u+r*Θ.lag 1 v ∧ 0≤Θ.lag (-(K : ℤ)) u+r*Θ.lag (-(K : ℤ)) v) ↔
      (-Θ.lag (-(K : ℤ)) u)/Θ.lag (-(K : ℤ)) v≤r ∧ r≤Θ.lag 1 u/(-Θ.lag 1 v) := by
  have h := Farey.twoLag_ratio_iff (A:=Θ.lag 1 u) (B:= -Θ.lag (-(K : ℤ)) u)
    (r:=r) (neg_pos.mpr hv.2) hv.1
  constructor
  · intro hh
    exact h.mp ⟨by nlinarith [hh.1],by nlinarith [hh.2]⟩
  · intro hh
    obtain ⟨h1,h2⟩ := h.mpr hh
    exact ⟨by nlinarith [h1],by nlinarith [h2]⟩

theorem pair_interval_nonempty_iff {Θ : Curve} {K : ℕ} {u v : Frequency}
    (hu : u∈plusSet Θ K) (hv : v∈minusSet Θ K) :
    ((-Θ.lag (-(K : ℤ)) u)/Θ.lag (-(K : ℤ)) v≤Θ.lag 1 u/(-Θ.lag 1 v)) ↔
      1≤plusRatio Θ K u*minusRatio Θ K v := by
  rw [div_le_div_iff₀ hv.1 (neg_pos.mpr hv.2)]
  unfold plusRatio minusRatio
  rw [div_mul_div_comm,le_div_iff₀ (mul_pos (neg_pos.mpr hu.2) (neg_pos.mpr hv.2))]
  ring_nf

theorem pairMeasure_program_iff {Θ : Curve} {K : ℕ}
    {u v : Frequency} (hv : v∈minusSet Θ K) (r : NNReal) :
    ProgramSolution Θ (pairLags K) (pairMeasure u v r) ↔
      0≤Θ.minimizer u+(r : ℝ)*Θ.minimizer v ∧
      (-Θ.lag (-(K : ℤ)) u)/Θ.lag (-(K : ℤ)) v≤(r : ℝ) ∧
        (r : ℝ)≤Θ.lag 1 u/(-Θ.lag 1 v) := by
  have hne : pairMeasure u v r≠0 := atomicMeasure_ne_zero _ _ (by simp [Fin.sum_univ_two])
  have hh := pair_ratio_constraints_iff (u:=u) hv (r : ℝ)
  constructor
  · intro h
    have h1 := h.2.2.2 1 (by simp [pairLags])
    have hK := h.2.2.2 (-(K : ℤ)) (by simp [pairLags])
    rw [pairMeasure_integral] at h1 hK
    exact ⟨by simpa only [pairMeasure_integral] using h.2.2.1,hh.mp ⟨h1,hK⟩⟩
  · rintro ⟨hmin,hint⟩
    obtain ⟨h1,hKm⟩ := hh.mpr hint
    refine ⟨inferInstance,hne,?_,?_⟩
    · rw [pairMeasure_integral]
      exact hmin
    · intro n hn
      simp only [pairLags,Set.mem_insert_iff,Set.mem_singleton_iff] at hn
      rw [pairMeasure_integral]
      rcases hn with rfl|rfl <;> assumption

/-- At the two ratio maximizers, the strictly positive minimizer slacks
make the two-atom converse a solution of the full two-lag program. -/
theorem feasible_of_ratio_product {Θ : Curve} {K : ℕ}
    {u v : Frequency} (hu : u∈plusSet Θ K) (hv : v∈minusSet Θ K)
    (hmin : 0<Θ.minimizer v) (hprod : 1≤plusRatio Θ K u*minusRatio Θ K v) :
    ∃r : NNReal,0<r ∧ ProgramSolution Θ (pairLags K) (pairMeasure u v r) ∧
      0<∫ω,Θ.minimizer ω∂pairMeasure u v r := by
  let t := (-Θ.lag (-(K : ℤ)) u)/Θ.lag (-(K : ℤ)) v
  have ht : 0<t := div_pos (neg_pos.mpr hu.2) hv.1
  let r : NNReal := ⟨t,ht.le⟩
  have hint : t≤Θ.lag 1 u/(-Θ.lag 1 v) := (pair_interval_nonempty_iff hu hv).mpr hprod
  have hmin' : 0<Θ.minimizer u+t*Θ.minimizer v :=
    add_pos (plus_minimizer_pos hu) (mul_pos ht hmin)
  exact ⟨r,ht,(pairMeasure_program_iff (u:=u) hv r).mpr ⟨hmin'.le,le_rfl,hint⟩,
    by rw [pairMeasure_integral];exact hmin'⟩

end polyak.ModeLocking.TwoLag
