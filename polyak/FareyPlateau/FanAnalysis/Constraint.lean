import polyak.FareyPlateau.FanAnalysis.ActualJets
import polyak.FareyPlateau.Fan.PolynomialJets
import polyak.FareyPlateau.FanAnalysis.ConvexLattice

/-! The full continuous phase constraint. Its frequency curvature is
explicit, jointly continuous and positive near both limiting zeros. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter Set
open scoped Topology

def constraint (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) : ℝ :=
  (m + z * δ) * (Real.cos (a δ) - Real.cos (θ - a δ)) +
    Real.cos (c δ) - Real.cos (m * θ + c δ)

def constraintFirst (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) : ℝ :=
  (m + z * δ) * Real.sin (θ - a δ) + m * Real.sin (m * θ + c δ)

def constraintSecond (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) : ℝ :=
  (m + z * δ) * Real.cos (θ - a δ) + m^2 * Real.cos (m * θ + c δ)

theorem constraint_scaled (m z τ y : ℝ) (a c : ℝ → ℝ) (δ : ℝ) :
    constraint m z a c δ (τ + y * δ) = scaledConstraint m z τ y a c δ := by
  unfold constraint scaledConstraint lagPath
  have he : -m * τ + (-m * y) * δ - c δ = -(m * (τ + y * δ) + c δ) := by ring
  rw [he, Real.cos_neg]
  ring

theorem hasDerivAt_constraint (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) :
    HasDerivAt (constraint m z a c δ) (constraintFirst m z a c δ θ) θ := by
  have ha := ((hasDerivAt_id θ).sub_const (a δ)).cos
  have hc := (((hasDerivAt_id θ).const_mul m).add_const (c δ)).cos
  have hd := (((hasDerivAt_const θ (Real.cos (a δ))).sub ha).const_mul (m + z * δ)).add_const (Real.cos (c δ))
  convert hd.sub hc using 1
  · funext x
    simp only [constraint, Pi.sub_apply, id_eq]
  · simp only [constraintFirst, id_eq, mul_one]
    ring

theorem hasDerivAt_constraintFirst (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) :
    HasDerivAt (constraintFirst m z a c δ) (constraintSecond m z a c δ θ) θ := by
  have ha := (((hasDerivAt_id θ).sub_const (a δ)).sin).const_mul (m + z * δ)
  have hc := ((((hasDerivAt_id θ).const_mul m).add_const (c δ)).sin).const_mul m
  convert ha.add hc using 1
  · rfl
  · simp only [constraintSecond, id_eq, mul_one]
    ring

theorem constraint_second (m z : ℝ) (a c : ℝ → ℝ) (δ θ : ℝ) :
    deriv^[2] (constraint m z a c δ) θ = constraintSecond m z a c δ θ := by
  have he : deriv (constraint m z a c δ) = constraintFirst m z a c δ := by
    funext θ
    exact (hasDerivAt_constraint m z a c δ θ).deriv
  change deriv (deriv (constraint m z a c δ)) θ = _
  rw [he]
  exact (hasDerivAt_constraintFirst m z a c δ θ).deriv

theorem continuousAt_constraintSecond {a c : ℝ → ℝ}
    (ha : ContinuousAt a 0) (hc : ContinuousAt c 0) (m z θ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => constraintSecond m z a c p.1 p.2) (0, θ) := by
  have ha' : ContinuousAt (fun p : ℝ × ℝ => a p.1) (0, θ) :=
    ha.comp_of_eq continuous_fst.continuousAt rfl
  have hc' : ContinuousAt (fun p : ℝ × ℝ => c p.1) (0, θ) :=
    hc.comp_of_eq continuous_fst.continuousAt rfl
  unfold constraintSecond
  fun_prop

theorem local_convex {a c : ℝ → ℝ} (ha : ContinuousAt a 0) (hc : ContinuousAt c 0)
    {m z θ₀ : ℝ} (hpos : 0 < constraintSecond m z a c 0 θ₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, |δ| < r →
      StrictConvexOn ℝ (Icc (θ₀ - r) (θ₀ + r)) (constraint m z a c δ) := by
  have he := (continuousAt_constraintSecond ha hc m z θ₀).eventually (eventually_gt_nhds hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε / 2, by positivity, ?_⟩
  intro δ hδ
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
    (fun x _ => (hasDerivAt_constraint m z a c δ x).continuousAt.continuousWithinAt)
  intro x hx
  rw [constraint_second]
  have hp : (δ, x) ∈ Metric.ball (0, θ₀) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    refine ⟨by linarith, ?_⟩
    have hxcc : x ∈ Icc (θ₀ - ε / 2) (θ₀ + ε / 2) := interior_subset hx
    rw [abs_lt]
    constructor <;> linarith [hxcc.1, hxcc.2]
  exact hball hp


end polyak.FareyPlateau.FanAnalysis
