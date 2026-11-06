import nesterov.Faithful.BelowWall
import nesterov.Slow.NegativeLead
import nesterov.Slow.RealQuadratic
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Article Theorem 5.4(c) and Corollary 5.5: necessary lead. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

/-- Negative effective lead produces a uniform quadratic instability margin,
and a genuine unbounded real scalar quadratic trajectory at every small ε. -/
theorem negative_lead_divergence
    (hlead : effectiveLead (F.u 0) F.q0 y<0) :
    ∃ lam∈Ioo (0:ℝ) 1,∃ r : ℝ,1<r ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      r<Rates.quadraticRate (F.method ε) (ε^2) 1 ∧
      1<Rates.rate (F.method ε) (ε^2) 1 ∧
      ∃ w : ℕ→ℝ,
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 (fun x : ℝ=>lam/2*‖x‖^2) ∧
        (F.method ε).IsTrajectory (gradient (fun x : ℝ=>lam/2*‖x‖^2)) w ∧
        ¬BddAbove (range (fun n=>‖w n‖)) := by
  obtain ⟨lam,hlam,r,hr,he⟩ := F.negative_lead_quadratic_lower hlead
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<min 1 (Real.sqrt lam) :=
    (eventually_lt_nhds (lt_min zero_lt_one (Real.sqrt_pos.2 hlam.1))).filter_mono nhdsWithin_le_nhds
  refine ⟨lam,hlam,r,hr,?_⟩
  filter_upwards [he,hsmall,self_mem_nhdsWithin] with ε hh hεb hε
  change 0<ε at hε
  have hε1 := hεb.trans_le (min_le_left _ _)
  have hμL : ε^2<1 := by nlinarith
  have hμlam : ε^2≤lam := by
    have hs := hεb.trans_le (min_le_right _ _)
    nlinarith [Real.sq_sqrt hlam.1.le,Real.sqrt_nonneg lam]
  obtain ⟨z,hz,hn,hq⟩ := hh
  exact ⟨hq,(hr.trans hq).trans_le (Rates.quadraticRate_le_rate _ (sq_pos_of_pos hε) hμL),
    Slow.exists_unbounded_real_quadratic _ (sq_pos_of_pos hε) hμL ⟨hμlam,hlam.2.le⟩ hz (hr.trans hn)⟩

/-- Literal liminf form of faithful(c), with extended-real liminf retaining
all possible unbounded rates. The preceding theorem supplies a finite margin. -/
theorem negative_lead_liminf
    (hlead : effectiveLead (F.u 0) F.q0 y<0) :
    (1:EReal)<liminf (fun ε=>(Rates.quadraticRate (F.method ε) (ε^2) 1:EReal)) (𝓝[>] (0:ℝ)) := by
  obtain ⟨_,_,r,hr,he⟩ := F.negative_lead_quadratic_lower hlead
  have hb : ∀ᶠ ε in 𝓝[>] (0:ℝ),(r:EReal)≤(Rates.quadraticRate (F.method ε) (ε^2) 1:EReal) :=
    he.mono fun _ h=>EReal.coe_le_coe_iff.mpr h.choose_spec.2.2.le
  exact (EReal.coe_lt_coe_iff.mpr hr).trans_le (Filter.le_liminf_of_le (by isBoundedDefault) hb)

/-- Quadratic stability forces nonnegative effective lead. Continuity is enough. -/
theorem necessary_lead_quadratic
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1) :
    0≤effectiveLead (F.u 0) F.q0 y := by
  by_contra h
  obtain ⟨_,_,r,hr,he⟩ := F.negative_lead_quadratic_lower (lt_of_not_ge h)
  obtain ⟨ε,hε⟩ := (he.and hs).exists
  obtain ⟨_,_,_,hq⟩ := hε.1
  exact not_lt_of_ge hε.2 (hr.trans hq)

/-- Uniform stability forces at least a half step of effective phase lead. -/
theorem necessary_lead
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.rate (F.method ε) (ε^2) 1≤1) :
    1/2≤effectiveLead (F.u 0) F.q0 y := by
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hq : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1 := by
    filter_upwards [hs,hsmall,self_mem_nhdsWithin] with ε he hε1 hε
    change 0<ε at hε
    exact (Rates.quadraticRate_le_rate _ (sq_pos_of_pos hε) (by nlinarith)).trans he
  have hnonneg := necessary_lead_quadratic F hq
  by_contra h
  have habs : |effectiveLead (F.u 0) F.q0 y|<1/2 := by rw [abs_of_nonneg hnonneg];exact lt_of_not_ge h
  obtain ⟨K,hK,hcontact⟩ := family_below_half F habs
  obtain ⟨ε,he⟩ := ((hcontact K le_rfl).2.and hs).exists
  obtain ⟨_,_,_,hr,_⟩ := he.1
  exact not_lt_of_ge he.2 hr

end
end nesterov.Faithful
