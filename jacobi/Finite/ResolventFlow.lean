import jacobi.Finite.AnalyticChart

/-!
The global spectral-weight construction of the resolvent flow.
Every real time is realized by the existing analytic inverse spectral
chart. Positivity, normalization, irreducibility and the prescribed
characteristic polynomial therefore hold by construction.
Use: ResolventLax identifies the tangent of this actual matrix family;
FlowBounds then estimates its actual Green energy.
Article: jacobi, Proposition 5.5, Equation (5.11).
Article role: the global positive-weight construction and its exact resolvent Lax equation.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev2 Real Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (S : Nodes (n+1))

/-- The fixed logarithmic weight velocity is minus twice the scaled
resolvent eigenvalue. It determines the time direction of the flow.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def resolventVelocity (k : Fin (n+1)) : ℝ :=
  -2/((n+1:ℝ)^2*(1-S.value k))

/-- The positive spectral probabilities at an arbitrary real flow time.
Using the global log chart avoids a local existence or continuation premise.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def resolventWeights (w : WeightSimplex (n+1)) (t : ℝ) : WeightSimplex (n+1) :=
  logWeights S (fun k => weightLogs S w k+t*resolventVelocity S k)

/-- The matrix flow through any member of the entire irreducible fibre.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def resolventFlow (J : Fiber (n+1) S.polynomial) (t : ℝ) : Fiber (n+1) S.polynomial :=
  reconstructFiber S (resolventWeights S (spectralWeights S J) t)

/-- Zero time recovers the initial probabilities exactly.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
@[simp] theorem resolventWeights_zero (w : WeightSimplex (n+1)) :
    resolventWeights S w 0=w := by
  simpa only [resolventWeights,zero_mul,add_zero] using logWeights_weightLogs S w

/-- The flow starts at the actual original matrix, including all its
Jacobi coefficients rather than merely an isospectral representative.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
@[simp] theorem resolventFlow_zero (J : Fiber (n+1) S.polynomial) :
    resolventFlow S J 0=J := by
  rw [resolventFlow,resolventWeights_zero,reconstruct_spectralWeights]

/-- Successive times add. The normalization discrepancy in the intermediate
logarithms is a common shift, which leaves every probability unchanged.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventWeights_add (w : WeightSimplex (n+1)) (s t : ℝ) :
    resolventWeights S (resolventWeights S w s) t=resolventWeights S w (s+t) := by
  unfold resolventWeights
  simp only [weightLogs_logWeights]
  have he : (fun k => weightLogs S w k+s*resolventVelocity S k-
      log (logNormalizer S (fun j => weightLogs S w j+s*resolventVelocity S j))+
      t*resolventVelocity S k)=
      (fun k => (weightLogs S w k+(s+t)*resolventVelocity S k)+
        -log (logNormalizer S (fun j => weightLogs S w j+s*resolventVelocity S j))) := by
    funext k
    ring
  rw [he,logWeights_shift]

/-- The reconstructed matrices form a global one-parameter group action
on the original fibre. Negative times give the inverse action.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_add (J : Fiber (n+1) S.polynomial) (s t : ℝ) :
    resolventFlow S (resolventFlow S J s) t=resolventFlow S J (s+t) := by
  simp only [resolventFlow,spectralWeights_reconstruct,resolventWeights_add]

/-- The first-site spectral probabilities of the actual matrix are exactly
the evolved probabilities, in the original prescribed eigenvalue order.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_weights (J : Fiber (n+1) S.polynomial) (t : ℝ) :
    spectralWeights S (resolventFlow S J t)=resolventWeights S (spectralWeights S J) t :=
  spectralWeights_reconstruct S _

/-- The matrix never leaves the prescribed polynomial fibre.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_charpoly (J : Fiber (n+1) S.polynomial) (t : ℝ) :
    (resolventFlow S J t).val.matrix.charpoly=J.val.matrix.charpoly :=
  (resolventFlow S J t).property.2.trans J.property.2.symm

/-- The resolvent trace is constant for all real times, before any
differentiation estimate is used.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_trace (J : Fiber (n+1) S.polynomial) (t : ℝ) :
    trace (resolventFlow S J t).val.green=trace J.val.green := by
  rw [green_trace _ (by rw [(resolventFlow S J t).property.2]; exact S.endpoint_pos.ne'),
    green_trace _ (by rw [J.property.2]; exact S.endpoint_pos.ne'),resolventFlow_charpoly]

/-- The evolving weights have the literal normalized exponential-tilt
formula. Characteristic-derivative factors cancel, so the initial weights
are the original matrix's weights rather than canonical weights.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventWeights_formula (w : WeightSimplex (n+1)) (t : ℝ) (k : Fin (n+1)) :
    (resolventWeights S w t).val k=
      w.val k*exp (t*resolventVelocity S k)/
        ∑ j,w.val j*exp (t*resolventVelocity S j) := by
  have he (j : Fin (n+1)) :
      exp (weightLogs S w j+t*resolventVelocity S j)*
        |S.polynomial.derivative.eval (S.value j)|⁻¹ =
      w.val j*exp (t*resolventVelocity S j) := by
    rw [exp_add,weightLogs,exp_log (mul_pos (w.property.1 j)
      (abs_pos.mpr (S.derivative_ne_zero j)))]
    field_simp [(abs_pos.mpr (S.derivative_ne_zero j)).ne']
  change (_*_⁻¹)/logNormalizer S _=_
  simp only [logNormalizer,he]

/-- The log-weight path is analytic at every real time. It supplies
analyticity of both the actual matrix and its actual Green energy.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventCoordinates_analytic (w : WeightSimplex (n+1)) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => fun k => weightLogs S w k+s*resolventVelocity S k) t := by
  apply AnalyticAt.pi
  intro k
  exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)

/-- Every entry of the actual flow matrix is analytic on the whole real
time axis. There is no unproved smooth-lift assumption.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_matrix_analytic (J : Fiber (n+1) S.polynomial) (t : ℝ)
    (i j : Fin (n+1)) :
    AnalyticAt ℝ (fun s => (resolventFlow S J s).val.matrix i j) t := by
  exact (logFiber_matrix_analytic S _ i j).comp
    (resolventCoordinates_analytic S (spectralWeights S J) t)

/-- The actual finite Green energy is analytic for every real flow time.
Used to differentiate twice and apply the genuine Taylor remainder bound.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventFlow_energy_analytic (J : Fiber (n+1) S.polynomial) (t : ℝ) :
    AnalyticAt ℝ (fun s => (resolventFlow S J s).val.energy) t := by
  exact (logEnergy_analytic S _).comp
    (resolventCoordinates_analytic S (spectralWeights S J) t)

end
end jacobi.Finite
