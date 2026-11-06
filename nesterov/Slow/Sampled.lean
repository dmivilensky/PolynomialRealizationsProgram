import nesterov.Slow.SampledLimits
import nesterov.Slow.QueryDictionary

/-!
Article: Lemma D.5. One fixed finite flow spectrum survives every sufficiently
small member of an arbitrary continuous second-order family.
-/
namespace nesterov.Slow
noncomputable section
open Spectral Filter Flow Set
open scoped Topology BigOperators NNReal
variable {θ y c : ℝ} (F : SecondOrderFamily θ y)

/-- The prescribed flow weights, exact forced charge, and strict reserve in
query normalization, before conversion back to latent amplitudes. -/
theorem sampled_flow_query_program (W : SpreadWitness θ y c) (hc : 0<c) (hb : 0≤θ-2*c) :
    let G := fun ε j=>F.slowG ε (SecondOrderFamily.slowPoint c (W.spectrum.frequency j))
    let S := fun ε j=>F.slowS ε (SecondOrderFamily.slowPoint c (W.spectrum.frequency j))
    let a := fun ε=>4*ε^2/F.stepAt ε
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      FiniteProgram W.spectrum.weight (fun j=>ε*W.spectrum.frequency j)
        (fun j=>a ε*G ε j) (fun j=>a ε*S ε j) (-c*ε)
        (a ε*sampleCharge W.spectrum.weight W.spectrum.frequency (S ε) c) ∧
      |a ε*sampleCharge W.spectrum.weight W.spectrum.frequency (S ε) c|<
        ∑ j,W.spectrum.weight j*(a ε*G ε j) := by
  apply sampled_program_forced_charge W hc hb
  · intro j
    exact F.slowG_physical_tendsto tendsto_id tendsto_const_nhds tendsto_const_nhds
  · intro j
    exact F.slowS_physical_tendsto tendsto_id tendsto_const_nhds tendsto_const_nhds
  · have hs := F.stepAt_tendsto.eventually (eventually_gt_nhds F.step_pos)
    filter_upwards [hs,self_mem_nhdsWithin] with ε hε he
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos he)) hε

theorem sampled_flow_feasible (W : SpreadWitness θ y c) (hc : 0<c) (hb : 0≤θ-2*c) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ (v : Fin W.J→ℝ≥0) (hv : ∑ j,v j=1) (C : ℝ),
      Feasible ((F.method ε).symbolPair (ε^2) 1 (-c*ε)) (-c*ε)
        (finiteSpectrum v (fun j=>Phase.frequency (ε*W.spectrum.frequency j)) hv) C ∧
      |C|<meanG (finiteSpectrum v (fun j=>Phase.frequency (ε*W.spectrum.frequency j)) hv)
        ((F.method ε).symbolPair (ε^2) 1 (-c*ε)) ∧
      ∀ j,0<v j := by
  let G := fun ε j=>F.slowG ε (SecondOrderFamily.slowPoint c (W.spectrum.frequency j))
  let S := fun ε j=>F.slowS ε (SecondOrderFamily.slowPoint c (W.spectrum.frequency j))
  let a := fun ε=>4*ε^2/F.stepAt ε
  have hεlim : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hstep : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<F.stepAt ε :=
    F.stepAt_tendsto.eventually (eventually_gt_nhds F.step_pos)
  have ha : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<a ε := by
    filter_upwards [hstep,self_mem_nhdsWithin] with ε he hε
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hε)) he
  have hprog := sampled_program_of_limits W hc hb G S a
    (fun j=>F.slowG_physical_tendsto tendsto_id tendsto_const_nhds tendsto_const_nhds)
    (fun j=>F.slowS_physical_tendsto tendsto_id tendsto_const_nhds tendsto_const_nhds) ha
  have hangle (j : Fin W.J) : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε*W.spectrum.frequency j∈Icc (0:ℝ) Real.pi := by
    have hh := hεlim.mul_const (W.spectrum.frequency j)
    simp only [zero_mul] at hh
    have htop : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε*W.spectrum.frequency j<Real.pi := by
      exact hh.eventually (eventually_lt_nhds Real.pi_pos)
    filter_upwards [htop,self_mem_nhdsWithin] with ε hεtop hε
    exact ⟨mul_nonneg hε.le (W.spectrum.frequency_nonneg j),hεtop.le⟩
  have hquery (j : Fin W.J) : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (F.u ε).eval₂ Complex.ofRealHom (F.wave ε (SecondOrderFamily.slowPoint c (W.spectrum.frequency j)))≠0 :=
    (F.query_wave_tendsto tendsto_id tendsto_const_nhds).eventually_ne (by norm_num)
  have hangles := Filter.eventually_all.mpr hangle
  have hqueries := Filter.eventually_all.mpr hquery
  have heps : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 := hεlim.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hprog,hangles,hqueries,hstep,heps,self_mem_nhdsWithin] with ε hp hω hU hstepε hε1 hε
  have he2 : ε^2≠1 := by
    have hpos : 0<ε := hε
    have hm := mul_pos hpos (sub_pos.mpr hε1)
    nlinarith
  let A := (F.method ε).symbolPair (ε^2) 1 (-c*ε)
  let f := fun j : Fin W.J=>Phase.frequency (ε*W.spectrum.frequency j)
  have hqg (j : Fin W.J) : queryG (A.u (f j)) (A.p (f j))=a ε*G ε j := by
    change 1-Complex.normSq (A.p (f j)/A.u (f j))=_
    rw [F.sampled_query_ratio (hω j) he2 (hU j)]
    exact (F.query_coefficients_exact hε.ne' he2 hstepε.ne' _).1
  have hqs (j : Fin W.J) : queryS (A.u (f j)) (A.p (f j))=a ε*S ε j := by
    change 2*(A.p (f j)/A.u (f j)).im=_
    rw [F.sampled_query_ratio (hω j) he2 (hU j)]
    exact (F.query_coefficients_exact hε.ne' he2 hstepε.ne' _).2
  obtain ⟨C,hpC,hsC⟩ := hp
  have hu : ∀ j,A.u (f j)≠0 := by
    intro j
    rw [F.sampled_query_value (hω j)]
    exact hU j
  have harc (j : Fin W.J) : Real.arccos (f j)=ε*W.spectrum.frequency j := Phase.arccos_frequency (hω j)
  have hpq : FiniteProgram W.spectrum.weight (fun j=>Real.arccos (f j))
      (fun j=>queryG (A.u (f j)) (A.p (f j))) (fun j=>queryS (A.u (f j)) (A.p (f j))) (-c*ε) C := by
    simpa only [harc,hqg,hqs] using hpC
  have hsq : |C|<∑ j,W.spectrum.weight j*queryG (A.u (f j)) (A.p (f j)) := by
    simpa only [hqg] using hsC
  obtain ⟨v,hv,C',hf,hs,hpos⟩ := query_to_latent_feasible W.spectrum.weight_nonneg W.spectrum.weight_sum
    f A (-c*ε) C hu hpq hsq
  refine ⟨v,hv,C',hf,hs,fun j=>hpos j ?_⟩
  rw [W.weight_eq]
  exact one_div_pos.mpr (Nat.cast_pos.mpr W.J_pos)

end
end nesterov.Slow
