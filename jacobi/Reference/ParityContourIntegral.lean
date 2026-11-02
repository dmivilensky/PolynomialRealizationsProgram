import jacobi.Reference.ParityContour

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The genuine normalized contour integrals are O(R_m^-1), uniformly
for the whole physical square. Their limit is zero. The contour
radius in energy is R_m^2, as in the article.
Use: parity_contour_integral_bound and parity_contour_integral_limit provide the analytic limit in the residue proof of Parity splitting.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine normalized parity contour integral on the original energy circle of radius R_m squared.
Use: parity_contour_integral_bound and parity_contour_integral_limit provide the analytic limit in the residue proof of Parity splitting.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def parityContourIntegral (a t s : ℝ) (m : ℕ) : ℂ :=
  (2*(Real.pi:ℂ)*Complex.I)⁻¹ •
    ∮ z in C((jacobi.Jacobi.endpointCorrection a:ℂ),(contourRadius a m)^2),parityIntegrand a t s z

/-- The genuine parity integrand has the inverse-cubic estimate at every point of the original energy circles.
Use: parity_contour_integral_bound applies the standard circle-integral norm bound directly in the original energy variable.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the square root of the actual shifted energy has norm R_m; evaluate the proved root-independent integrand estimate at that genuine root. -/
theorem parity_integrand_energy_circle_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∃ M : ℕ,∀ m : ℕ,M≤m →
      ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      ∀ z∈Metric.sphere (jacobi.Jacobi.endpointCorrection a:ℂ) ((contourRadius a m)^2),
        ‖parityIntegrand a t s z‖≤B/(contourRadius a m)^3 := by
  -- The original energy circle is covered completely, including its two real intersections.
  obtain ⟨B,hB,M,hbound⟩ := parity_integrand_contour_bound ha
  refine ⟨B,hB,M,fun m hm t ht s hs z hz => ?_⟩
  let w := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hw : w^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ) := frequency_square _
  have hR : 0<contourRadius a m := contourRadius_pos ha m
  have hn : ‖w‖=contourRadius a m := by
    rw [Metric.mem_sphere,dist_eq_norm] at hz
    have hh := congrArg norm hw
    rw [norm_pow,hz] at hh
    nlinarith [norm_nonneg w]
  have hh := hbound m hm w hn t ht s hs
  have he : (jacobi.Jacobi.endpointCorrection a:ℂ)+w^2=z := by rw [hw]; ring
  rwa [he] at hh

/-- The actual normalized contour integrals have a uniform inverse-radius bound on the whole physical square.
Use: parity_contour_integral_limit proves convergence to zero for the original integrals, before their identification with signed kernel partial sums by residues.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: apply the community circle-integral norm estimate to the proved genuine inverse-cubic pointwise bound; the energy-circle radius is R_m^2. -/
theorem parity_contour_integral_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∃ M : ℕ,∀ m : ℕ,M≤m →
      ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
        ‖parityContourIntegral a t s m‖≤B/contourRadius a m := by
  obtain ⟨B,hB,M,hbound⟩ := parity_integrand_energy_circle_bound ha
  refine ⟨B,hB,M,fun m hm t ht s hs => ?_⟩
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (sq_nonneg (contourRadius a m)) (hbound m hm t ht s hs)
  change ‖parityContourIntegral a t s m‖≤_ at h
  exact h.trans_eq (by field_simp [(contourRadius_pos ha m).ne'])

/-- The genuine normalized contour integrals tend to zero for every pair of physical half-interval points.
Use: the residue identity then forces the original absolutely convergent signed kernel series to sum to zero in Parity splitting.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the original radius is at least m+1, so the proved inverse-radius bound is dominated by B/(m+1), whose limit is zero. -/
theorem parity_contour_integral_limit {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    Tendsto (parityContourIntegral a t s) atTop (𝓝 0) := by
  -- No numerical threshold is assumed: the bound's finite threshold is already proved from the actual functions.
  obtain ⟨B,hB,M,hbound⟩ := parity_contour_integral_bound ha
  have hd : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' ?_ (hd.const_div_atTop B)
  filter_upwards [eventually_ge_atTop M] with m hm
  exact (hbound m hm t ht s hs).trans
    (div_le_div_of_nonneg_left hB.le (by positivity : 0<(m:ℝ)+1) (contourRadius_index_le ha m))

end
end jacobi.Reference
