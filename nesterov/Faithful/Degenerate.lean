import nesterov.Faithful.BelowWall

/-! The negative-leading-term branch at the half-step wall. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Polynomial Asymptotics
open scoped Topology

/-- The leading-term convention in the article, stated with its literal
O(ω^(2p+2)) remainder. -/
def HasLeadingEvenTerm (u q : Polynomial ℝ) (p : ℕ) (s : ℝ) : Prop :=
  s≠0 ∧ (fun ω : ℝ=>limitSymbol u q ω-s*ω^(2*p))=O[𝓝 (0:ℝ)] (fun ω : ℝ=>ω^(2*p+2))

theorem leading_even_ratio {u q : Polynomial ℝ} {p : ℕ} {s : ℝ}
    (h : HasLeadingEvenTerm u q p s) :
    Tendsto (fun ω : ℝ=>limitSymbol u q ω/ω^(2*p)) (𝓝[>] (0:ℝ)) (𝓝 s) := by
  have ho := h.2.trans_isLittleO (isLittleO_pow_pow (by omega : 2*p<2*p+2))
  have ht := ho.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hh := ht.add_const s
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  change 0<ω at hω
  field_simp [hω.ne']
  ring

theorem negative_leading_symbol {u q : Polynomial ℝ} {p : ℕ} {s : ℝ}
    (h : HasLeadingEvenTerm u q p s) (hs : s<0) :
    ∀ᶠ ω in 𝓝[>] (0:ℝ),limitSymbol u q ω<0 := by
  have ht := (leading_even_ratio h).eventually (eventually_lt_nhds hs)
  filter_upwards [ht,self_mem_nhdsWithin] with ω he hω
  change 0<ω at hω
  have hh := (div_lt_iff₀ (pow_pos hω (2*p))).mp he
  simpa only [zero_mul] using hh

theorem angle_tendsto_zero (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    Tendsto (limitAngle u q) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hω : Tendsto (fun ω : ℝ=>ω) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have ht := ((phase_lead_limit u q hy hu hq).mono_left (nhdsGT_le_nhdsNE (0:ℝ))).mul hω
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact div_mul_cancel₀ _ (ne_of_gt hω)

/-- At the degenerate half-step wall, a negative leading term bends the
principal phase strictly below ω/2 at every sufficiently small positive ω. -/
theorem half_negative_phase {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)
    (hτ : effectiveLead (F.u 0) F.q0 y=1/2) {p : ℕ} {s : ℝ}
    (hterm : HasLeadingEvenTerm (F.u 0) F.q0 p s) (hs : s<0) :
    ∀ᶠ ω in 𝓝[>] (0:ℝ),|limitAngle (F.u 0) F.q0 ω|<ω/2 := by
  have hratio := (phase_lead_limit (F.u 0) F.q0 F.step_pos (F.u_one 0) F.q0_one).mono_left
    (nhdsGT_le_nhdsNE (0:ℝ))
  rw [hτ] at hratio
  have hlo := hratio.eventually (eventually_gt_nhds (by norm_num : (1/4:ℝ)<1/2))
  have hup := (angle_tendsto_zero (F.u 0) F.q0 F.step_pos (F.u_one 0) F.q0_one).eventually
    (eventually_lt_nhds (by positivity : (0:ℝ)<Real.pi/2))
  have hωpi : ∀ᶠ ω in 𝓝[>] (0:ℝ),ω<Real.pi :=
    (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds
  filter_upwards [negative_leading_symbol hterm hs,hlo,hup,hωpi,self_mem_nhdsWithin]
    with ω hS hl hu hωp hω
  change 0<ω at hω
  have hangle : 0<limitAngle (F.u 0) F.q0 ω := by
    have hh := (lt_div_iff₀ hω).mp hl
    nlinarith
  rw [abs_of_pos hangle]
  by_contra hn
  have hd : 0≤limitAngle (F.u 0) F.q0 ω-ω/2 := by linarith [le_of_not_gt hn]
  have hdp : limitAngle (F.u 0) F.q0 ω-ω/2≤Real.pi := by linarith [Real.pi_pos]
  have hsin := Real.sin_nonneg_of_mem_Icc ⟨hd,hdp⟩
  have hid := Phase.stationary_lag_one_phase_identity (F.method 0) (by norm_num : (0:ℝ)<1)
    (show ω∈Icc (0:ℝ) Real.pi from ⟨hω.le,hωp.le⟩)
  change ((1-circle ω)*(F.method 0).characteristic 0 (circle ω)*
    star ((F.method 0).characteristic 1 (circle ω))).re=_ at hid
  rw [mul_assoc,←limitProduct_characteristic (F.method 0) F.q0 F.initial_factor] at hid
  have ha := family_limit_angle F (Phase.frequency ω)
  rw [Phase.arccos_frequency ⟨hω.le,hωp.le⟩] at ha
  have ha' : Phase.angle (Spectral.g ((F.method 0).symbolPair 0 1 0) (Phase.frequency ω))
    (Spectral.skew ((F.method 0).symbolPair 0 1 0) (Phase.frequency ω))=limitAngle (F.u 0) F.q0 ω := by
    simpa only [familyPair,zero_pow (by decide : 2≠0)] using ha
  rw [ha'] at hid
  have hm : 0≤Phase.magnitude
      (Spectral.g ((F.method 0).symbolPair 0 1 0) (Phase.frequency ω))
      (Spectral.skew ((F.method 0).symbolPair 0 1 0) (Phase.frequency ω)) := Real.sqrt_nonneg _
  have hsinhalf : 0≤Real.sin (ω/2) := Real.sin_nonneg_of_mem_Icc ⟨by linarith,by linarith⟩
  have hnonneg : 0≤limitSymbol (F.u 0) F.q0 ω := by rw [show limitSymbol (F.u 0) F.q0 ω=_ from hid];positivity
  linarith


/-- Every sufficiently small positive-frequency contact yields the full
quantified planar instability conclusion of faithful(b). -/
theorem family_resonance_of_small_contacts {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)
    (hphase : ∀ᶠ ω in 𝓝[>] (0:ℝ),|limitAngle (F.u 0) F.q0 ω|<ω/2) :
    ∃ K₀ : ℕ,3≤K₀ ∧ ∀ K : ℕ,K₀≤K →
      |limitAngle (F.u 0) F.q0 (2*Real.pi/K)|<Real.pi/K ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ t : ℝ,0<t ∧
        Spectral.Feasible ((F.method ε).symbolPair (ε^2) 1 t) t
          (Phase.singletonSpectrum (Phase.frequency (2*Real.pi/K))) 0 ∧
        1<Rates.rate (F.method ε) (ε^2) 1 ∧
        ∃ (f : EuclideanSpace ℝ (Fin 2)→ℝ) (x : ℕ→EuclideanSpace ℝ (Fin 2)),
          polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ (F.method ε).IsTrajectory (gradient f) x ∧
          ∀ k : ℕ,‖x k‖=Real.exp (k*t) := by
  have hc := reciprocal_frequency_tendsto.eventually hphase
  have hn := (reciprocal_frequency_tendsto.mono_right (nhdsGT_le_nhdsNE (0:ℝ))).eventually
    (limitProduct_eventually_ne_zero F)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc.and hn)
  refine ⟨max 3 N,le_max_left _ _,fun K hK=>?_⟩
  have hK3 : 3≤K := (le_max_left _ _).trans hK
  have hKN : N≤K := (le_max_right _ _).trans hK
  have hKp : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  let ω := 2*Real.pi/(K:ℝ)
  let c := Phase.frequency ω
  have hω0 : 0<ω := div_pos (by positivity) hKp
  have hωpi : ω<Real.pi := by
    apply (div_lt_iff₀ hKp).mpr
    have hh : (3:ℝ)≤K := by exact_mod_cast hK3
    nlinarith [Real.pi_pos]
  have hω : Real.arccos c=ω := Phase.arccos_frequency ⟨hω0.le,hωpi.le⟩
  have hz : polyak.Waves.z 0 (Real.arccos c)=circle ω := by rw [hω];simp [circle,polyak.Waves.z]
  have hp : (F.method 0).characteristic 0 (polyak.Waves.z 0 (Real.arccos c))*
      star ((F.method 0).characteristic 1 (polyak.Waves.z 0 (Real.arccos c)))≠0 := by
    rw [hz,←limitProduct_characteristic (F.method 0) F.q0 F.initial_factor]
    exact (hN K hKN).2
  have hpcontact : |limitAngle (F.u 0) F.q0 (2*Real.pi/K)|<Real.pi/K := by
    convert (hN K hKN).1 using 1
    ring
  refine ⟨hpcontact,?_⟩
  apply fast_resonance F (j:=1) (by simp) hK3 c
  · simpa [ω] using hω
  · exact limit_pair_nonzero F c hp
  · rw [family_limit_angle,hω]
    exact hpcontact

/-- The half-degenerate branch of faithful(b), retaining the article's exact
leading even term hypothesis and requiring only family continuity. -/
theorem family_half_negative {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)
    (hτ : effectiveLead (F.u 0) F.q0 y=1/2) {p : ℕ} {s : ℝ}
    (hterm : HasLeadingEvenTerm (F.u 0) F.q0 p s) (hs : s<0) :
    ∃ K₀ : ℕ,3≤K₀ ∧ ∀ K : ℕ,K₀≤K →
      |limitAngle (F.u 0) F.q0 (2*Real.pi/K)|<Real.pi/K ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ t : ℝ,0<t ∧
        Spectral.Feasible ((F.method ε).symbolPair (ε^2) 1 t) t
          (Phase.singletonSpectrum (Phase.frequency (2*Real.pi/K))) 0 ∧
        1<Rates.rate (F.method ε) (ε^2) 1 ∧
        ∃ (f : EuclideanSpace ℝ (Fin 2)→ℝ) (x : ℕ→EuclideanSpace ℝ (Fin 2)),
          polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ (F.method ε).IsTrajectory (gradient f) x ∧
          ∀ k : ℕ,‖x k‖=Real.exp (k*t) :=
  family_resonance_of_small_contacts F (half_negative_phase F hτ hterm hs)

end
end nesterov.Faithful
