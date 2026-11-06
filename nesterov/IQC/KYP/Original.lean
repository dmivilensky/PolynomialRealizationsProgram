import nesterov.IQC.KYP.Convergence
import nesterov.IQC.KYP.LagOne
import nesterov.Stationary.Centering

/-! The finite certificate Lyapunov theorem for the original objective and minimizer. -/
namespace nesterov.IQC.KYP.LyapunovData
noncomputable section
open scoped BigOperators
variable {A : StationaryMethod} {μ L t : ℝ} {M : ℕ}
variable {cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t}
variable (D : LyapunovData A μ L t M cert)

/-- The from-rest Lyapunov norm bound uses the actual original objective,
actual minimizer and actual stationary execution, in arbitrary Hilbert spaces. -/
theorem original_fromRest_norm_bound (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius A μ L<Real.exp t) (hM : ∀ n∈cert.lags,n≤M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E→ℝ} (hf : polyak.SmoothStronglyConvex μ L f)
    (xstar : E) (hmin : ∀ x,f xstar≤f x)
    (w : ℕ→E) (hw : A.IsTrajectory (gradient f) w) (x0 : E)
    (hinit : ∀ j : Fin A.memory,w j.val=x0) (k : ℕ) :
    ‖w k-xstar‖≤D.restConstant*(Real.exp t)^k*‖x0-xstar‖ := by
  have hc : polyak.CenteredSmoothStronglyConvex μ L (polyak.centerObjective f xstar) := by
    refine ⟨hf.centerObjective xstar,by simp [polyak.centerObjective],?_⟩
    rw [(polyak.hasGradientAt_centerObjective hf.differentiable xstar 0).gradient]
    simpa using (hf.minimizer_iff xstar).mp hmin
  have ht:=hw.centerObjective A hf.differentiable xstar
  exact D.fromRest_norm_bound hμ hμL hr hM hc (fun k=>w k-xstar) ht (x0-xstar)
    (fun j=>by rw [hinit]) k

end
end nesterov.IQC.KYP.LyapunovData

namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators

/-- The lag-one potential correction is exactly the original-objective term
printed in Proposition lyap, with the real query error and minimizer value. -/
theorem lagOne_original_correction {A : StationaryMethod} {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hlags : cert.lags={1}) (hα : cert.α 1=Real.exp t) (hβ : cert.β 1=0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E→ℝ) (xstar : E) (w : ℕ→E) (k : ℕ) :
    -sourcePotential cert (fun n=>polyak.normalizeFunction μ L (polyak.centerObjective f xstar)
      (A.query (fun j=>w j-xstar) n)) k=
        4/(L-μ)*(f (A.query w k)-f xstar-(L+μ)/4*‖A.query w k-xstar‖^2) := by
  rw [sourcePotential_lagOne cert hlags hα hβ]
  rw [show -(2*polyak.normalizeFunction μ L (polyak.centerObjective f xstar)
      (A.query (fun j=>w j-xstar) k))=
      -2*polyak.normalizeFunction μ L (polyak.centerObjective f xstar)
        (A.query (fun j=>w j-xstar) k) from by ring]
  rw [normalized_value_correction,A.query_sub_const]
  simp only [polyak.centerObjective,add_sub_cancel]

end
end nesterov.IQC.KYP
