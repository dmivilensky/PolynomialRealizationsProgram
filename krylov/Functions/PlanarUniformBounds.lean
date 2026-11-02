import krylov.Functions.PlanarFiniteRadius

/-!
Article: main_krylov, thm:Fplanar, uniform genuine planar polynomial bounds.
Use: control the entire true binary cubic ball without any regularity
assumption on the observation-dependent fibre centre. Source: the proved
coefficient disks, finite-dimensional compactness and polynomial homogeneity.
-/
namespace krylov.Functions
noncomputable section
open Set Metric NormedSpace krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The genuine four coefficients as a finite normed coordinate vector.
Article: main_krylov, thm:Fplanar. -/
def binaryCoefficientVector (t : krylov.Tensor.BinaryCubic) : Fin 4 → ℝ := ![t.t0,t.t1,t.t2,t.t3]

/-- Reconstruct the genuine binary cubic from its four real coefficients.
Article: main_krylov, thm:Fplanar. -/
def binaryFromVector (q : Fin 4 → ℝ) : krylov.Tensor.BinaryCubic := ⟨q 0,q 1,q 2,q 3⟩

/-- Exact reconstruction of all four true coefficients.
Article: main_krylov, thm:Fplanar. -/
theorem binaryFromVector_coefficientVector (t : krylov.Tensor.BinaryCubic) :
    binaryFromVector (binaryCoefficientVector t)=t := by cases t; rfl

/-- The original diagonal tensor ball lies in the actual coefficient unit cube.
Article: main_krylov, thm:Fplanar. -/
theorem binaryCoefficientVector_bound {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) :
    ‖binaryCoefficientVector t‖≤1 := by
  obtain ⟨h0,h3⟩ := axis_bounds ht
  have hd := coefficient_disks ht
  have h1 : |t.t1|≤1 := by nlinarith only [hd.1,sq_nonneg t.t0,sq_abs t.t1,abs_nonneg t.t1]
  have h2 : |t.t2|≤1 := by nlinarith only [hd.2,sq_nonneg t.t1,sq_abs t.t2,abs_nonneg t.t2]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  fin_cases i
  · simpa [binaryCoefficientVector] using h0
  · simpa [binaryCoefficientVector] using h1
  · simpa [binaryCoefficientVector] using h2
  · simpa [binaryCoefficientVector] using h3

/-- All actual terminal operators and common observed gradients are uniformly
bounded on the full genuine cubic ball. Article: main_krylov, thm:Fplanar. -/
theorem planeTerminal_uniform_bounds (r : ℝ) :
    ∃ M : ℝ, 0<M ∧ ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖planeTerminalOperator r t‖≤M ∧ ‖planeTerminalRho r t‖≤M := by
  have hL : Continuous (fun q : Fin 4 → ℝ=>planeTerminalOperator r (binaryFromVector q)) := by
    unfold planeTerminalOperator binaryFromVector planeOfPair
    fun_prop
  have hρ : Continuous (fun q : Fin 4 → ℝ=>planeTerminalRho r (binaryFromVector q)) := by
    unfold planeTerminalRho binaryFromVector planeOfPair
    fun_prop
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0 : Fin 4 → ℝ) 1).exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Fin 4 → ℝ) 1).exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨|A|+|B|+1,by positivity,?_⟩
  intro t ht
  have hm : binaryCoefficientVector t∈closedBall (0 : Fin 4 → ℝ) 1 := by
    simpa only [mem_closedBall,dist_zero_right] using binaryCoefficientVector_bound ht
  have ha := hA _ hm
  have hb := hB _ hm
  rw [binaryFromVector_coefficientVector] at ha hb
  exact ⟨ha.trans (by linarith only [le_abs_self A,abs_nonneg B]),
    hb.trans (by linarith only [le_abs_self B,abs_nonneg A])⟩

/-- The actual homogeneous gradient of every true admissible cubic has a
uniform global quadratic bound. Article: main_krylov, thm:Fplanar.
Compactness is used only on actual coefficient vectors and unit directions. -/
theorem planeCubic_homogeneous_uniform_bound (r : ℝ) :
    ∃ B : ℝ, 0<B ∧ ∀ t : krylov.Tensor.BinaryCubic, t.InBall → ∀ v : Plane,
      ‖planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v))‖≤B*‖v‖^2 := by
  let F := fun z : (Fin 4 → ℝ) × Plane =>
    planeOfPair (planarValueCoordinateDerivative 0 r (binaryFromVector z.1) (pairOfPlane z.2))
  have hc : Continuous F := by unfold F planeOfPair planarValueCoordinateDerivative binaryFromVector pairOfPlane; fun_prop
  obtain ⟨A,hA⟩ := ((isCompact_closedBall (0 : Fin 4 → ℝ) 1).prod
    (isCompact_closedBall (0 : Plane) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|A|+1,by positivity,?_⟩
  intro t ht v
  by_cases hv : v=0
  · subst v
    simp [pairOfPlane,planarValueCoordinateDerivative,planeOfPair]
  have hm : (binaryCoefficientVector t,normalize v)∈
      closedBall (0 : Fin 4 → ℝ) 1 ×ˢ closedBall (0 : Plane) 1 := by
    constructor
    · simpa only [mem_closedBall,dist_zero_right] using binaryCoefficientVector_bound ht
    · simp only [mem_closedBall,dist_zero_right,norm_normalize hv,le_refl]
  have hh := hA _ hm
  change ‖planeOfPair (planarValueCoordinateDerivative 0 r
    (binaryFromVector (binaryCoefficientVector t)) (pairOfPlane (normalize v)))‖≤A at hh
  rw [binaryFromVector_coefficientVector] at hh
  have he : planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v))=
      ‖v‖^2 • planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane (normalize v))) := by
    have hs : pairOfPlane v=‖v‖ • pairOfPlane (normalize v) := by
      have hh := congrArg pairOfPlane (norm_smul_normalize v)
      exact hh.symm
    rw [hs]
    have hz := planarValueCoordinateDerivative_scale 0 r ‖v‖ t (pairOfPlane (normalize v))
    rw [mul_zero] at hz
    rw [hz,planeOfPair_smul]
  rw [he,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (hh.trans (by linarith only [le_abs_self A])) (sq_nonneg _)).trans_eq (mul_comm _ _)

end
end krylov.Functions
