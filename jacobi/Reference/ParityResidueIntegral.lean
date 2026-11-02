import jacobi.Reference.ParityResidues
import jacobi.Reference.ParityContourIntegral
import jacobi.Reference.ContourPoles
import jacobi.Complex.IndexedResidues

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Pole enumeration, simplicity, boundary exclusions and normalization
are all proved for the actual original characteristic functions.
Use: parity_splitting combines this identity with the genuine vanishing contour limit and absolute convergence of the original GL summands.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter Metric _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every sufficiently large original normalized parity contour integral is exactly minus kappa times the corresponding original signed kernel partial sum.
Use: parity_splitting combines this identity with the genuine vanishing contour limit and absolute convergence of the original GL summands.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the finite simple-pole residue theorem proved from Cauchy--Goursat in Complex.FiniteResidues.
Proof: apply the indexed residue theorem separately to the actual sigma and tau characteristic quotients. Their genuine pole sets have exactly indices zero through m. Subtract the two integrals and use the already proved exact signed residue coefficient for each original kernel summand. -/
theorem parity_contour_residue_identity {a : ℝ} (ha : -1<a) :
    ∃ M : ℕ,∀ m : ℕ,M≤m → ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      parityContourIntegral a t s m=
        -((2*Real.pi^2*normConstant a:ℝ):ℂ)*
          ((∑ k∈Finset.range (m+1),(-1:ℝ)^k* jacobi.GelfandLevitan.kernelTerm a ha k t s:ℝ):ℂ) := by
  classical
  -- Separate residue applications retain coincident target/reference zeros without a union-pole convention.
  obtain ⟨M₁,hpoles⟩ := contour_spectral_poles ha
  obtain ⟨D,_hD,M₂,hcomparison⟩ := contour_characteristic_bound ha
  refine ⟨max M₁ M₂,fun m hm t ht s hs => ?_⟩
  let c : ℂ := (jacobi.Jacobi.endpointCorrection a:ℂ)
  let R : ℝ := (contourRadius a m)^2
  let g : ℂ → ℂ := fun z => solution a z t*solution a z s
  have hR : 0<R := sq_pos_of_pos (contourRadius_pos ha m)
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := fun z _ =>
    (solution_energy_analytic_half ha ht z).mul (solution_energy_analytic_half ha hs z)
  have hp := hpoles m ((le_max_left _ _).trans hm)
  have hS := jacobi.Complex.indexed_simple_residues (jacobi.Bessel.sigma a ha)
    (jacobi.Bessel.sigma_strictMono ha) (m+1) hR hg
    (fun z _ => characteristicSigma_analytic a z) (characteristicSigma_zero_iff ha)
    (fun k => characteristicSigma_simple ha ((characteristicSigma_zero_iff ha _).mpr ⟨k,rfl⟩))
    (fun k => by simpa only [Nat.lt_succ_iff] using (hp k).1.1)
    (fun k => by simpa only [Nat.lt_succ_iff] using (hp k).1.2)
  have hT := jacobi.Complex.indexed_simple_residues (eigenvalue a)
    (eigenvalue_strictMono ha) (m+1) hR hg
    (fun z _ => characteristicTau_analytic a z) (characteristicTau_zero_iff a)
    (fun k => characteristicTau_simple ha ((characteristicTau_zero_iff a _).mpr ⟨k,rfl⟩))
    (fun k => by simpa only [Nat.lt_succ_iff] using (hp k).2.1)
    (fun k => by simpa only [Nat.lt_succ_iff] using (hp k).2.2)
  have hquotS : CircleIntegrable (fun z => g z/characteristicSigma a z) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hz' : ‖z-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hn := (hcomparison m ((le_max_right _ _).trans hm) z hz').1
    exact ((hg z (sphere_subset_closedBall hz)).continuousAt.div
      (characteristicSigma_analytic a z).continuousAt hn).continuousWithinAt
  have hquotT : CircleIntegrable (fun z => g z/characteristicTau a z) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hz' : ‖z-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hz
    exact ((hg z (sphere_subset_closedBall hz)).continuousAt.div
      (characteristicTau_analytic a z).continuousAt
      (characteristicTau_contour_ne_zero ha m hz')).continuousWithinAt
  have he : parityIntegrand a t s=(fun z => g z/characteristicSigma a z-g z/characteristicTau a z) := by
    funext z
    dsimp [parityIntegrand,g]
    ring
  rw [parityContourIntegral,he,circleIntegral.integral_sub hquotS hquotT,smul_sub,hS,hT,
    ← Finset.sum_sub_distrib]
  rw [Complex.ofReal_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact parity_residue_term ha k t s

end
end jacobi.Reference
