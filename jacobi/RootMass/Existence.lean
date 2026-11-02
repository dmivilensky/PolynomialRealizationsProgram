import jacobi.RootMass.Bounds
import jacobi.Variational.MomentExistence

/-!
Article: jacobi, Appendix D.5 (unrestricted inner problem).
A narrow box proves genuine finite-cost feasibility for every T>0. A
minimizing sequence is rearranged without changing its complete objective.
The proved coercivity bounds mass, energy and root mass; the existing Helly
compactness constructs a limit. Fatou for the whole nonnegative polynomial
objective then proves actual attainment, including negative mass multipliers.
Source: the direct method, reusing the compactness and rearrangement theorems of jacobi.
Use: gives finite inner objective for the original explicit spectral-feasibility construction.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual narrow box has a genuine integrable square root.
Use: gives finite inner objective for the original explicit spectral-feasibility construction.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: its square root is the constant square-root height on the same finite compact interval. -/
theorem narrowBox_root_integrable (M r : ℝ) (hM : 0≤M) (hr : 0<r) :
    Integrable (fun x => sqrt ((narrowBox M r hM hr).value x)) := by
  have he : (fun x => sqrt ((narrowBox M r hM hr).value x))=
      (Icc (-r) r).indicator (fun _ : ℝ => sqrt (M/(2*r))) := by
    funext x
    by_cases hx : x∈Icc (-r) r <;> simp [narrowBox,hx]
  rw [he]
  exact (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc

/-- Every positive inner second-moment threshold has an actual finite root-energy competitor.
Use: proves nonemptiness and finiteness before selecting an inner minimizing sequence.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: choose mass sqrt(T)+1. Exponential continuity supplies a sufficiently
small positive box width whose actual spectral second moment exceeds T.
The literal box has integrable root, mass and energy. -/
theorem inner_feasible {T : ℝ} (hT : 0<T) :
    ∃ m : RootDensity,T≤observe m.toDensity .second := by
  -- The feasible moment is bounded through the actual kernel, not a proxy spectrum.
  let M := sqrt T+1
  have hM : 0<M := by dsimp only [M]; positivity
  have hsub : T<M^2 := by dsimp only [M]; nlinarith [sq_sqrt hT.le,sqrt_nonneg T]
  have he : ∀ᶠ r : ℝ in 𝓝 0,T<exp (-4*r)*M^2 :=
    (show Continuous (fun r : ℝ => exp (-4*r)*M^2) by fun_prop).continuousAt.eventually
      (lt_mem_nhds (by simpa only [mul_zero,neg_zero,exp_zero,one_mul] using hsub))
  have he' : ∀ᶠ r : ℝ in 𝓝[Ioi 0] 0,T<exp (-4*r)*M^2 ∧ r∈Ioi 0 :=
    (he.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨r,hr,hrp⟩ := he'.exists
  exact ⟨⟨narrowBox M r hM.le hrp,narrowBox_root_integrable M r hM.le hrp⟩,
    hr.le.trans (narrowBox_second_lower M r hM.le hrp)⟩

/-- The true inner variational problem is attained at an actual nonzero symmetric decreasing density for every T>0.
Use: the compact-profile and exact quadrature proof starts with a constructed optimizer, not an assumed existence certificate.
Article: jacobi, Appendix D.5 (unrestricted inner problem).
Proof: choose a decreasing actual cost sequence and rearrange it preserving
the complete objective. Coercivity supplies all three norm bounds. Existing
compactness and Fatou construct an actual finite-root-energy limit, preserve
the spectral constraint, and identify its true cost with the original infimum. -/
theorem inner_minimizer_exists {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T) :
    ∃ m : RootDensity,SymmetricDecreasing m.value ∧ 0<m.mass ∧ T≤observe m.toDensity .second ∧
      m.cost a b=inner a b T := by
  -- A minimizing sequence is selected from the literal original admissible set.
  let A := (fun m : RootDensity => m.cost a b) '' {m | T≤observe m.toDensity .second}
  obtain ⟨w,hw⟩ := inner_feasible hT
  have hA : A.Nonempty := ⟨w.cost a b,w,hw,rfl⟩
  obtain ⟨u,huanti,hu,humem⟩ := exists_seq_tendsto_sInf hA (OrderBot.bddBelow A)
  choose m hm hc using humem
  choose r hrs hrF hrG using fun n => (m n).radial_replacement a b
  have hrCost (n : ℕ) : (r n).cost a b=u n :=
    (congrArg ENNReal.ofReal (hrF n)).trans (hc n)
  have hu0 : u 0≠∞ := by rw [← hrCost 0]; exact ENNReal.ofReal_ne_top
  have hF (n : ℕ) : (r n).objective a b≤(u 0).toReal := by
    rw [← (r n).cost_toReal ha hb.le,hrCost]
    exact ENNReal.toReal_mono hu0 (huanti (Nat.zero_le n))
  have hbounds (n : ℕ) := (r n).objective_bounds ha hb (hF n)
  obtain ⟨φ,hφ,q,hqs,_hqM,_hqE,hpoint,_hqcost,_hqroot,hobs⟩ :=
    compact_subsequence (fun n => (r n).toDensity) hrs (fun n => (hbounds n).2.2) (fun n => (hbounds n).1)
  have hpae : ∀ᵐ x,Tendsto (fun n => (r (φ n)).value x) atTop (𝓝 (q.value x)) := by
    have hz : ∀ᵐ x : ℝ,x≠0 := by simp [ae_iff]
    exact hz.mono hpoint
  -- The limiting root integrability is proved by Fatou, not included as a compactness premise.
  obtain ⟨hi,_hroot⟩ := integrable_limit_of_bound
    (fun n => (r (φ n)).root_integrable)
    (fun n => continuous_sqrt.measurable.comp (r (φ n)).measurable)
    (fun _ _ => sqrt_nonneg _) (continuous_sqrt.measurable.comp q.measurable)
    (fun _ => sqrt_nonneg _) (hpae.mono fun _ hx => continuous_sqrt.continuousAt.tendsto.comp hx)
    (fun n => (hbounds (φ n)).2.1)
  let p : RootDensity := ⟨q,hi⟩
  have hpT : T≤observe p.toDensity .second := ge_of_tendsto (hobs .second)
    (Eventually.of_forall fun n => (hm (φ n)).trans (hrG (φ n)))
  have hpCost : p.cost a b≤liminf (fun n => (r (φ n)).cost a b) atTop := by
    simp_rw [RootDensity.cost_eq_lintegral _ ha hb.le]
    exact continuous_integrand_liminf (fun n => (r (φ n)).measurable) hpae
      (fun v => ENNReal.ofReal (f a b (sqrt v))) (ENNReal.continuous_ofReal.comp (by unfold f; fun_prop))
  have hlim : liminf (fun n => (r (φ n)).cost a b) atTop=inner a b T := by
    simp_rw [hrCost]
    exact (hu.comp hφ.tendsto_atTop).liminf_eq
  rw [hlim] at hpCost
  have hlo : inner a b T≤p.cost a b := sInf_le ⟨p,hpT,rfl⟩
  exact ⟨p,hqs,mass_pos_of_observe_pos p.toDensity .second (hT.trans_le hpT),hpT,le_antisymm hpCost hlo⟩

end
end jacobi.RootMass
