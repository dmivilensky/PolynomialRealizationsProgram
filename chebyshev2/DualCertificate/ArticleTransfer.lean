import chebyshev2.DualCertificate.UniformCertificate

/-!
Article: chebyshev2, Theorem E.1, the uniform certificate-value limit.
`Data.packed_value_uniform` turns convergence along every fiber section into a uniform
absolute-error bound over the entire fiber. Together with `Data.admissible_stable`, it
is the exact transfer statement used in the proof chain of Theorem 3.6(ii).
Use: `packedValue` names the actual value already appearing in `Data.packed_value_tendsto`;
the proof reuses `uniform_lower_of_all_sections` on the negative absolute error.
Source: chebyshev2, Appendix E.3 — uniform transfer by testing arbitrary fiber sections.
-/
namespace chebyshev2.DualCertificate.Data
noncomputable section
open Filter Real chebyshev2.Packing chebyshev2.Calibration.Data
open scoped Topology
set_option autoImplicit false

/--
Formula (30) at the actual packed density, with its own ground parameter.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem E.1, the uniform certificate-value limit.

Source: chebyshev2, Appendix E.3 — uniform transfer by testing arbitrary fiber sections.
-/
def packedValue (D : chebyshev2.DualCertificate.Data) {n : ℕ}
    (J : chebyshev2.Fiber (n+1)) : ℝ :=
  D.analytic.value (packedCoupling_positive J.val (by omega) J.property)
    (packedLogDeterminant J.val (by omega) J.property 32)
    (packedLogDeterminant J.val (by omega) J.property 64)
    (packedLogDeterminant J.val (by omega) J.property
      (D.calibration.sigma*packedCoupling J.val (by omega) J.property))
    ((packedCoupling J.val (by omega) J.property)^2/4*
      ∑' j,packedEigenvalue J.val (by omega) J.property j^2)

/--
Theorem E.1's uniform value clause, without an admissibility premise.

Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop,∀ J :
chebyshev2.Fiber (n+1), |D.packedValue J-D.analytic.targetValue|≤ε`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem E.1, the uniform certificate-value limit.

Source: chebyshev2, Appendix E.3 — uniform transfer by testing arbitrary fiber sections.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem packed_value_uniform (D : chebyshev2.DualCertificate.Data)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ J : chebyshev2.Fiber (n+1),
      |D.packedValue J-D.analytic.targetValue|≤ε := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have ht : ∀ J : ∀ n : ℕ,chebyshev2.Fiber (n+1),
      Tendsto (fun n => -|D.packedValue (J n)-D.analytic.targetValue|) atTop (𝓝 (0:ℝ)) := by
    intro J
    -- Every section has vanishing absolute error. Negating the error puts this
    -- two-sided approximation into the one-sided uniform-section lemma's format.
    simpa only [packedValue,sub_self,abs_zero,neg_zero] using
      ((D.packed_value_tendsto J).sub
        (tendsto_const_nhds (x := D.analytic.targetValue))).abs.neg
  filter_upwards [uniform_lower_of_all_sections
    (fun n => ⟨chebyshev2.SineJacobi.fiber (n+1) (by omega)⟩)
    (v := fun _ J => -|D.packedValue J-D.analytic.targetValue|) ht hε] with n hn J
  have h := hn J
  -- The uniform lower bound -ε ≤ -|error| is precisely |error| ≤ ε.
  linarith

end
end chebyshev2.DualCertificate.Data
