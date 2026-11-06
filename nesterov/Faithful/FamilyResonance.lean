import nesterov.Faithful.Resonance
import nesterov.Slow.Continuity

/-! Theorem faithful(d), with only the source coefficient continuity. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Spectral Phase
open scoped Topology NNReal
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

def familyPair (ε : ℝ) : SymbolPair := (F.method ε).symbolPair (ε^2) 1 0

theorem familyPair_u_tendsto (c : Frequency) :
    Tendsto (fun ε=>(familyPair F ε).u c) (𝓝[>] (0:ℝ)) (𝓝 ((familyPair F 0).u c)) :=
  by
    simpa only [familyPair,StationaryMethod.symbolPair_u,Polynomial.eval_map] using
      F.u_eval_tendsto (z:=fun _=>polyak.Waves.z 0 (Real.arccos c)) tendsto_const_nhds

theorem familyPair_p_tendsto (c : Frequency) :
    Tendsto (fun ε=>(familyPair F ε).p c) (𝓝[>] (0:ℝ)) (𝓝 ((familyPair F 0).p c)) := by
  have he (ε : ℝ) := (F.method ε).normalizedPolynomial_complex_eval (ε^2) 1
    (polyak.Waves.z 0 (Real.arccos c))
  simp_rw [familyPair,StationaryMethod.symbolPair_p,he]
  have hε : Tendsto (fun ε : ℝ=>ε^2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hid : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.pow 2
  have hu := F.u_eval_tendsto (z:=fun _=>polyak.Waves.z 0 (Real.arccos c)) tendsto_const_nhds
  have hv := F.v_eval_tendsto (z:=fun _=>polyak.Waves.z 0 (Real.arccos c)) tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℝ=>(1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 1) := tendsto_const_nhds
  have h2 : Tendsto (fun _ : ℝ=>(2:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 2) := tendsto_const_nhds
  have ha := (h1.add hε).div (h1.sub hε) (by norm_num : (1:ℝ)-0≠0)
  have hb := h2.div (h1.sub hε) (by norm_num : (1:ℝ)-0≠0)
  convert! ((ha.ofReal.mul hu).sub (hb.ofReal.mul hv)) using 1 <;>
    simp only [Slow.SecondOrderFamily.u,Slow.SecondOrderFamily.v,Polynomial.eval_map,
    zero_pow (by decide : 2≠0),add_zero,sub_zero,div_one,Complex.ofReal_one,one_mul,Pi.div_apply]

theorem familyPair_g_tendsto (c : Frequency) :
    Tendsto (fun ε=>g (familyPair F ε) c) (𝓝[>] (0:ℝ)) (𝓝 (g (familyPair F 0) c)) := by
  exact ((Complex.continuous_normSq.tendsto _).comp (familyPair_u_tendsto F c)).sub
    ((Complex.continuous_normSq.tendsto _).comp (familyPair_p_tendsto F c))

theorem familyPair_skew_tendsto (c : Frequency) :
    Tendsto (fun ε=>skew (familyPair F ε) c) (𝓝[>] (0:ℝ)) (𝓝 (skew (familyPair F 0) c)) := by
  exact Complex.continuous_im.continuousAt.tendsto.comp
    ((familyPair_p_tendsto F c).mul (familyPair_u_tendsto F c).star)

/-- A strict fast rational resonance of the actual limit method gives a
single growing real planar objective for each sufficiently small ε. -/
theorem fast_resonance {j K : ℕ} (hcop : j.Coprime K) (hK : 3≤K)
    (c : Frequency) (hω : Real.arccos c=2*Real.pi*j/K)
    (hne : g (familyPair F 0) c≠0 ∨ skew (familyPair F 0) c≠0)
    (hphase : |angle (g (familyPair F 0) c) (skew (familyPair F 0) c)|<Real.pi/K) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ t : ℝ,0<t ∧
      Feasible ((F.method ε).symbolPair (ε^2) 1 t) t (singletonSpectrum c) 0 ∧
      1<Rates.rate (F.method ε) (ε^2) 1 ∧
      ∃ (f : EuclideanSpace ℝ (Fin 2)→ℝ) (x : ℕ→EuclideanSpace ℝ (Fin 2)),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ (F.method ε).IsTrajectory (gradient f) x ∧
        ∀ k : ℕ,‖x k‖=Real.exp (k*t) := by
  have hphaseε := eventually_strict_phase hK (familyPair F) (familyPair F 0) c
    (familyPair_g_tendsto F c) (familyPair_skew_tendsto F c) hne hphase
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),0<ε := self_mem_nhdsWithin
  have hεone : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),ε<1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hphaseε,hεpos,hεone] with ε hp hε hε1
  have hμ : 0<ε^2 := sq_pos_of_pos hε
  have hμL : ε^2<1 := by nlinarith
  exact growing_planar_of_phase (F.method ε) hμ hμL hcop hK c hω (Or.inl hp.1.ne') hp.2


/-- The literal nonzero endpoint-product hypothesis implies a nonzero
spectral phase pair, with no query-zero exclusion. -/
theorem limit_pair_nonzero (c : Frequency)
    (hne : (F.method 0).characteristic 0 (polyak.Waves.z 0 (Real.arccos c))*
      star ((F.method 0).characteristic 1 (polyak.Waves.z 0 (Real.arccos c)))≠0) :
    g (familyPair F 0) c≠0 ∨ skew (familyPair F 0) c≠0 := by
  by_contra hh
  push Not at hh
  have hf := Phase.stationary_factor (F.method 0) (μ:=0) (L:=1) (by norm_num) 0 c
  simp only [familyPair,zero_pow (by decide : 2≠0)] at hh
  rw [hh.1,hh.2] at hf
  norm_num at hf
  rcases hf with hf|hf
  · exact hne (by rw [hf,zero_mul])
  · exact hne (by rw [hf,star_zero,mul_zero])

end
end nesterov.Faithful
