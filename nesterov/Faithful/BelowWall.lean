import nesterov.Faithful.SourcePhase
import nesterov.Faithful.FamilyResonance
import Mathlib.Topology.Algebra.Order.Field

/-! The rational low-frequency phase contacts used by faithful(b). -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Polynomial
open scoped Topology

theorem reciprocal_frequency_tendsto :
    Tendsto (fun K : ℕ=>2*Real.pi/(K:ℝ)) atTop (𝓝[>] (0:ℝ)) := by
  have hn : Tendsto (fun K : ℕ=>(K:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun K : ℕ=>2*Real.pi/(K:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop hn
  apply tendsto_nhdsWithin_iff.mpr ⟨ht,?_⟩
  change ∀ᶠ K : ℕ in atTop,0<2*Real.pi/(K:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
  exact div_pos (by positivity) (by exact_mod_cast (zero_lt_one.trans_le hK))

/-- A strict sub-half-step limiting phase gives every sufficiently large
rational contact, with one common lower threshold for the period. -/
theorem phase_contacts_of_limit {P : ℝ→ℝ} {τ : ℝ}
    (ht : Tendsto (fun ω : ℝ=>P ω/ω) (𝓝[≠] (0:ℝ)) (𝓝 τ)) (hτ : |τ|<1/2) :
    ∃ K₀ : ℕ,3≤K₀ ∧ ∀ K : ℕ,K₀≤K → |P (2*Real.pi/K)|<Real.pi/K := by
  have hlim := ht.comp (reciprocal_frequency_tendsto.mono_right (nhdsGT_le_nhdsNE (0:ℝ)))
  have hsmall : ∀ᶠ K : ℕ in atTop,|P (2*Real.pi/K)/(2*Real.pi/K)|<1/2 :=
    hlim.abs.eventually (gt_mem_nhds hτ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsmall
  refine ⟨max 3 N,le_max_left _ _,fun K hK=>?_⟩
  have hK3 : 3≤K := (le_max_left _ _).trans hK
  have hK0 : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hω : 0<2*Real.pi/(K:ℝ) := div_pos (by positivity) hK0
  have hh := hN K ((le_max_right _ _).trans hK)
  rw [abs_div,abs_of_pos hω] at hh
  have hh' := (div_lt_iff₀ hω).mp hh
  convert hh' using 1
  ring

theorem below_half_contacts (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) (hτ : |effectiveLead u q y|<1/2) :
    ∃ K₀ : ℕ,3≤K₀ ∧ ∀ K : ℕ,K₀≤K →
      |limitAngle u q (2*Real.pi/K)|<Real.pi/K :=
  phase_contacts_of_limit (phase_lead_limit u q hy hu hq) hτ


/-- The full strict-half-step branch of faithful(b), with the period chosen
before ε and a genuine fixed real planar witness at each admissible ε. -/
theorem family_below_half {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)
    (hτ : |effectiveLead (F.u 0) F.q0 y|<1/2) :
    ∃ K₀ : ℕ,3≤K₀ ∧ ∀ K : ℕ,K₀≤K →
      |limitAngle (F.u 0) F.q0 (2*Real.pi/K)|<Real.pi/K ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ t : ℝ,0<t ∧
        Spectral.Feasible ((F.method ε).symbolPair (ε^2) 1 t) t
          (Phase.singletonSpectrum (Phase.frequency (2*Real.pi/K))) 0 ∧
        1<Rates.rate (F.method ε) (ε^2) 1 ∧
        ∃ (f : EuclideanSpace ℝ (Fin 2)→ℝ) (x : ℕ→EuclideanSpace ℝ (Fin 2)),
          polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ (F.method ε).IsTrajectory (gradient f) x ∧
          ∀ k : ℕ,‖x k‖=Real.exp (k*t) := by
  obtain ⟨N,hN3,hN⟩ := below_half_contacts (F.u 0) F.q0 F.step_pos (F.u_one 0) F.q0_one hτ
  have hnonzero := (reciprocal_frequency_tendsto.mono_right (nhdsGT_le_nhdsNE (0:ℝ))).eventually
    (limitProduct_eventually_ne_zero F)
  obtain ⟨M,hM⟩ := eventually_atTop.mp hnonzero
  refine ⟨max N M,hN3.trans (le_max_left _ _),fun K hK=>?_⟩
  have hNK := (le_max_left _ _).trans hK
  have hK3 := hN3.trans hNK
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
    exact hM K ((le_max_right _ _).trans hK)
  refine ⟨hN K hNK,?_⟩
  apply fast_resonance F (j:=1) (by simp) hK3 c
  · simpa [ω] using hω
  · exact limit_pair_nonzero F c hp
  · rw [family_limit_angle,hω]
    exact hN K hNK

end
end nesterov.Faithful
