import jacobi.Variational.AmplitudeMoments
import jacobi.Variational.ClosedLowerConstant

/-!
The homogeneous lower bound at the one-quarter Nesterov edge.
Multiply actual density competitors by four: mass and the top threshold
gain four, the second moment gains sixteen, and energy gains eight.
The exact full Fredholm scaling also retains every pole. Taking actual
infima and the full Fredholm supremum yields the required lower constant.
Use: AllThreeTerm combines this bound with the padded residual spectrum
and the endpoint identity a^2=4E. No root-mass homogeneity is used.
Article: jacobi, Theorem 5.3.
Article role: amplitude scaling and the one-eighth homogeneous lower bound at the quarter spectrum.
-/
namespace jacobi.Variational
noncomputable section
open Real Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The actual edge spectrum divided by four, in the shared interface.
Article: jacobi, Theorem 5.3.
-/
def quarterEdge (Λ : EdgeSpectrum) : EdgeSpectrum := Λ.scale (1/4) (by norm_num)

/-- Multiplying an actual density by four multiplies its true cost by
eight, with the positive real-power normalization evaluated exactly.
Article: jacobi, Theorem 5.3.
-/
theorem Density.scale_four_cost (q : Density) :
    (q.scale 4 (by norm_num)).cost=8*q.cost := by
  have hp : (4:ℝ)^(3/2:ℝ)=8 := by
    rw [show (3/2:ℝ)=(3:ℝ)*(1/2) by ring,rpow_mul (by norm_num),← sqrt_eq_rpow]
    norm_num
  rw [Density.cost,Density.scale_energy,hp,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤8)]
  norm_num only [ENNReal.ofReal_ofNat]
  rfl

/-- A proved four-amplitude lift bounds an actual competitor infimum.
The empty-set case and infinite infima are included by the complete order.
Article: jacobi, Theorem 5.3.
-/
theorem eighth_infimum_le_of_lift (I : ℝ≥0∞) (A : Set Density)
    (h : ∀ q∈A,I≤(q.scale 4 (by norm_num)).cost) :
    (1/8:ℝ≥0∞)*I≤sInf (Density.cost '' A) := by
  apply le_sInf
  rintro x ⟨q,hq,rfl⟩
  have he := mul_le_mul_of_nonneg_left (h q hq) (show (0:ℝ≥0∞)≤1/8 from bot_le)
  rw [Density.scale_four_cost,← mul_assoc] at he
  norm_num only [one_div] at he
  rw [ENNReal.inv_mul_cancel (by norm_num : (8:ℝ≥0∞)≠0) (by norm_num : (8:ℝ≥0∞)≠∞),one_mul] at he
  simpa only [one_div] using he

/-- Every exact-mass root-constrained competitor at the quarter edge
lifts to a feasible competitor of each original moment relaxation.
The root constraint is dropped, precisely as required for these branches.
Article: jacobi, Theorem 5.3.
-/
theorem quarter_moment_lower (Λ : EdgeSpectrum) (A : Set Observation) :
    (1/8:ℝ≥0∞)*relaxedInfimum A Λ.mass (threshold Λ)≤
      rootInfimum A (quarterEdge Λ).mass (threshold (quarterEdge Λ)) := by
  apply eighth_infimum_le_of_lift
  intro q hq
  apply sInf_le
  refine ⟨q.scale 4 (by norm_num),⟨?_,?_⟩,rfl⟩
  · rw [Density.scale_mass,hq.1,quarterEdge,EdgeSpectrum.scale_mass]
    linarith
  · have hmass : 0<q.mass := by
      rw [hq.1,quarterEdge,EdgeSpectrum.scale_mass]
      exact mul_pos (by norm_num) Λ.mass_pos
    intro i hi
    have hobs := hq.2.2 i hi
    cases i with
    | second =>
      rw [Density.scale_second]
      change (quarterEdge Λ).second≤observe q .second at hobs
      rw [quarterEdge,EdgeSpectrum.scale_second] at hobs
      change Λ.second≤4^2*observe q .second
      nlinarith
    | top =>
      rw [Density.scale_top q hmass 4 (by norm_num)]
      change (1/4:ℝ)*Λ.value 0≤observe q .top at hobs
      change Λ.value 0≤4*observe q .top
      linarith

/-- Every actual quarter-edge Fredholm competitor lifts to the original
parameter s. This is valid also at an infinite target or a spectral pole.
Article: jacobi, Theorem 5.3.
-/
theorem quarter_fredholm_lower (Λ : EdgeSpectrum) {s : ℝ} (hs : 0≤s) :
    (1/8:ℝ≥0∞)*fredholmInfimum s Λ.mass (Λ.fredholm s)≤
      rootFredholmInfimum (4*s) (quarterEdge Λ).mass ((quarterEdge Λ).fredholm (4*s)) := by
  apply eighth_infimum_le_of_lift
  intro q hq
  apply sInf_le
  refine ⟨q.scale 4 (by norm_num),⟨?_,?_⟩,rfl⟩
  · rw [Density.scale_mass,hq.1,quarterEdge,EdgeSpectrum.scale_mass]
    linarith
  · rw [Density.scale_fredholm q 4 (by norm_num) hs]
    have hf := hq.2.2
    rw [quarterEdge,EdgeSpectrum.scale_fredholm,
      show (1/4:ℝ)*(4*s)=s by ring] at hf
    exact hf

/-- The entire homogeneous lower constant transfers at the quarter
edge with its exact one-eighth energy factor. All finite candidates and
all three continuum branches are retained; the root-mass branch is absent.
Article: jacobi, Theorem 5.3.
-/
theorem closed_quarter_lowerConstant_transfer (N : ℕ → ℕ)
    (S : ∀ n,jacobi.Finite.ClosedNodes (N n)) (hN : ∀ n,0<N n)
    (hNlim : Tendsto N atTop atTop) (Λ : EdgeSpectrum)
    (hd : Tendsto (fun n => distance (jacobi.Finite.closedFibreSpectrum (S n))
      (quarterEdge Λ).value) atTop (𝓝 0)) :
    (1/8:ℝ≥0∞)*homogeneousLowerConstant Λ≤
      liminf (fun n => closedFibreEnergyInfimum (S n)) atTop := by
  obtain ⟨hm,hF⟩ := closed_fibre_transfer N S hN hNlim (quarterEdge Λ) hd
  unfold homogeneousLowerConstant
  rw [mul_max,mul_max]
  apply max_le
  · apply max_le
    · exact (quarter_moment_lower Λ {Observation.second}).trans (hm {Observation.second})
    · have he : jacobi.Keller.Kel (Λ.value 0) Λ.mass=
          relaxedInfimum {Observation.top} Λ.mass (threshold Λ) := by
        unfold jacobi.Keller.Kel relaxedInfimum
        congr 1
        ext m
        simp only [mem_singleton_iff,forall_eq,threshold]
      rw [he]
      exact (quarter_moment_lower Λ {Observation.top}).trans (hm {Observation.top})
  · rw [ENNReal.mul_iSup]
    exact iSup_le (fun s => (quarter_fredholm_lower Λ s.property.1.le).trans
      (hF (4*s.val) (mul_nonneg (by norm_num) s.property.1.le)))

end
end jacobi.Variational
