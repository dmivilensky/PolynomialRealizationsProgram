import krylov.Information.PhysicalCentre
import krylov.Information.MetricSlack
import krylov.Reference.CanonicalSteps

/-!
Article: main_krylov, thm:centre, normalized physical information radius.
Use: apply the proved robust two-scenario estimate and seminorm reflection
bound to the actual constructed physical centre and its actual twin operators.
Source: genuine positive-root coordinate cancellation and the existing exact
terminal information-radius inequalities. Admissibility is a separate obligation.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- Canonical form normalization has exactly the original physical action after changing the input by the true metric root.
Use: convert actual physical residual norms to the source's genuine canonical two-scenario problem.
Article: main_krylov, thm:centre, Δ̂A₀¹ᐟ²u=A₀^(−1/2)Δu.
Proof: cancel the actual right inverse metric root against its actual root in the physical matrix product. -/
theorem canonical_form_action (G B : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) :
    cgOperator (relativeOperator G B) (cgOperator (metricRoot G) u)=
      cgOperator (metricRoot G)⁻¹ (cgOperator B u) := by
  have he : relativeOperator G B*metricRoot G=(metricRoot G)⁻¹*B := by
    simp only [relativeOperator,Matrix.mul_assoc,nonsing_inv_mul _ (metricRoot_det_unit G hG),Matrix.mul_one]
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (relativeOperator G B)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot G) u)=_
  rw [← mul_apply_eq_comp,← map_mul,he,map_mul,mul_apply_eq_comp]
  rfl

/-- The actual canonical relative form of a nonsingular physical centre is nonsingular.
Use: the normalized robust radius uses a derived inverse domain.
Article: main_krylov, thm:centre, invertibility of Ĵ.
Proof: both genuine inverse-root determinants and the actual physical centre determinant are units. -/
theorem relative_centre_unit (G J : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (hJ : IsUnit J.det) : IsUnit (relativeOperator G J).det := by
  have hi := (metricRoot G).isUnit_nonsing_inv_det (metricRoot_det_unit G hG)
  simp only [relativeOperator,det_mul]
  exact (hi.mul hJ).mul hi

/-- Every common physical correction obeys the normalized robust lower bound for two opposite physical centre errors.
Use: the source metric is the original physical positive base throughout both residuals.
Article: main_krylov, thm:centre, normalized residual radius before substituting the actual twin.
Proof: use the existing exact robust matrix bound in the genuine normalized
coordinates. The true metric root transports the common physical correction,
and the actual inverse-root action transports both real residuals exactly. -/
theorem normalized_two_scenario_lower (G J Δ : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hJ : IsUnit J.det) (g u : EuclideanSpace ℝ (Fin n)) :
    let K := cgOperator (relativeOperator G Δ*(relativeOperator G J)⁻¹)
    ‖K (cgOperator (metricRoot G)⁻¹ g)‖/Real.sqrt (1+‖K‖^2)≤
      max ‖cgOperator (metricRoot G)⁻¹ (g+cgOperator (J+Δ) u)‖
        ‖cgOperator (metricRoot G)⁻¹ (g+cgOperator (J-Δ) u)‖ := by
  -- The physical correction is changed by the actual metric root, not by an arbitrary whitening map.
  have hp : relativeOperator G (J+Δ)=relativeOperator G J+relativeOperator G Δ := by
    simp only [relativeOperator,Matrix.mul_add,Matrix.add_mul]
  have hm : relativeOperator G (J-Δ)=relativeOperator G J-relativeOperator G Δ := by
    simp only [relativeOperator,Matrix.mul_sub,Matrix.sub_mul]
  have h := terminal_two_scenario_lower (relativeOperator G J) (relativeOperator G Δ)
    (relative_centre_unit G J hG hJ) (cgOperator (metricRoot G)⁻¹ g) (cgOperator (metricRoot G) u)
  rw [← hp,← hm] at h
  change ‖cgOperator (relativeOperator G Δ*(relativeOperator G J)⁻¹)
      (cgOperator (metricRoot G)⁻¹ g)‖/
      Real.sqrt (1+‖cgOperator (relativeOperator G Δ*(relativeOperator G J)⁻¹)‖^2)≤
    max ‖cgOperator (metricRoot G)⁻¹ g+
      cgOperator (relativeOperator G (J+Δ)) (cgOperator (metricRoot G) u)‖
      ‖cgOperator (metricRoot G)⁻¹ g+
        cgOperator (relativeOperator G (J-Δ)) (cgOperator (metricRoot G) u)‖ at h
  rw [canonical_form_action G (J+Δ) hG,canonical_form_action G (J-Δ) hG] at h
  simpa only [map_add] using h

/-- The robust normalized numerator is exactly the actual centre correction's hidden-curvature action.
Use: identify the inverse-model radius formula with the source's physical centred-update formula.
Article: main_krylov, thm:centre, ‖Δ̂Ĵ⁻¹ρ‖=‖Δ̂A₀¹ᐟ²u_c‖.
Proof: the genuine inverse relative-form identity transports the actual
physical inverse centre. Its true metric root cancels its true inverse;
the centre update contributes only a minus sign, which disappears in the norm. -/
theorem normalized_centre_numerator (G J Δ : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖cgOperator (relativeOperator G Δ*(relativeOperator G J)⁻¹)
      (cgOperator (metricRoot G)⁻¹ g)‖=
    ‖cgOperator (relativeOperator G Δ)
      (cgOperator (metricRoot G) (-(cgOperator J⁻¹ g)))‖ := by
  -- Transport the actual inverse centre through the genuine root, then remove only its final minus sign.
  have hi : Matrix.toEuclideanCLM (𝕜 := ℝ) (relativeOperator G J)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot G)⁻¹ g)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot G)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ g) := by
    rw [relativeOperator_inv G J hG,← mul_apply_eq_comp,← map_mul]
    have he : (metricRoot G*J⁻¹*metricRoot G)*(metricRoot G)⁻¹=metricRoot G*J⁻¹ := by
      simp only [Matrix.mul_assoc,mul_nonsing_inv _ (metricRoot_det_unit G hG),Matrix.mul_one]
    rw [he,map_mul,mul_apply_eq_comp]
  simp only [cgOperator,map_mul,mul_apply_eq_comp,hi,map_neg,norm_neg]

/-- The source's centred-update normalized lower bound holds for every common physical correction.
Use: express the genuine robust radius through u_c=−J⁻¹g and the original positive metric.
Article: main_krylov, thm:centre, the displayed normalized lower bound with u_c.
Proof: substitute the proved genuine centre-numerator identity into the
already proved physical normalized two-scenario inequality. -/
theorem normalized_centred_lower (G J Δ : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hJ : IsUnit J.det) (g u : EuclideanSpace ℝ (Fin n)) :
    let K := cgOperator (relativeOperator G Δ*(relativeOperator G J)⁻¹)
    ‖cgOperator (relativeOperator G Δ) (cgOperator (metricRoot G) (-(cgOperator J⁻¹ g)))‖/
      Real.sqrt (1+‖K‖^2)≤
      max ‖cgOperator (metricRoot G)⁻¹ (g+cgOperator (J+Δ) u)‖
        ‖cgOperator (metricRoot G)⁻¹ (g+cgOperator (J-Δ) u)‖ := by
  have h := normalized_two_scenario_lower G J Δ hG hJ g u
  dsimp only at h ⊢
  rwa [normalized_centre_numerator G J Δ hG g] at h

/-- The actual constructed physical twin satisfies the source's normalized residual lower radius for every common correction.
Use: apply the robust obstruction to the real information-preserving pair,
whose centre is computed solely from its actual physical probes.
Article: main_krylov, thm:centre, the displayed normalized physical lower bound.
Proof: the genuine terminal reflection gives B♯=2J_D−B. Thus the actual
operators are precisely J_D±(B−J_D); apply the proved normalized robust
two-scenario theorem in the genuine original positive physical base. -/
theorem Scenario.physical_twin_normalized_lower {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm)
    (hG : (S.inPhysical D).base.PosDef) (hJ : IsUnit (S.physicalCentre D).det)
    (g u : EuclideanSpace ℝ (Fin (N+1))) :
    let G := (S.inPhysical D).base
    let J := S.physicalCentre D
    let Δ := (S.inPhysical D).lastOperator N-J
    let K := cgOperator (relativeOperator G Δ*(relativeOperator G J)⁻¹)
    ‖K (cgOperator (metricRoot G)⁻¹ g)‖/Real.sqrt (1+‖K‖^2)≤
      max ‖cgOperator (metricRoot G)⁻¹ (g+cgOperator ((S.inPhysical D).lastOperator N) u)‖
        ‖cgOperator (metricRoot G)⁻¹
          (g+cgOperator (((S.reflect N).inPhysical D).lastOperator N) u)‖ := by
  -- The two real terminal operators are the actual opposite deviations about the data-only physical model.
  have hplus : S.physicalCentre D+((S.inPhysical D).lastOperator N-S.physicalCentre D)=
      (S.inPhysical D).lastOperator N := by abel
  have hminus : S.physicalCentre D-((S.inPhysical D).lastOperator N-S.physicalCentre D)=
      ((S.reflect N).inPhysical D).lastOperator N := by
    rw [S.physical_reflect_about_centre D hD hA hE,two_smul]
    abel
  have h := normalized_two_scenario_lower (S.inPhysical D).base (S.physicalCentre D)
    ((S.inPhysical D).lastOperator N-S.physicalCentre D) hG hJ g u
  simpa only [hplus,hminus] using h

/-- Every actual physical twin pair retains its full seminorm radius about the data centre under an arbitrary alternative estimate.
Use: specialize the reflected-fibre centre principle to the actual physical operators and their true data-only centre.
Article: main_krylov, thm:centre, every-seminorm physical centre inequality.
Proof: the actual terminal reflection is the exact partner required by the
already proved seminorm reflection inequality. -/
theorem Scenario.physical_twin_seminorm {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm)
    (ν : Seminorm ℝ (Matrix (Fin (N+1)) (Fin (N+1)) ℝ))
    (J : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    ν ((S.inPhysical D).lastOperator N-S.physicalCentre D)≤
      max (ν ((S.inPhysical D).lastOperator N-J))
        (ν (((S.reflect N).inPhysical D).lastOperator N-J)) := by
  rw [S.physical_reflect_about_centre D hD hA hE]
  exact reflected_seminorm ν _ _ J

end
end krylov.Information
