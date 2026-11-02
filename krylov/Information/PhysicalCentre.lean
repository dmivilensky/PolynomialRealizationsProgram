import krylov.Information.CentreModel
import krylov.Secant.Canonical

/-!
Article: main_krylov, thm:centre, arbitrary physical direction coordinates.
Use: transport the constructed coordinate involution to genuine physical
operators and identify its centre from the actual probe observations.
Source: reuse the existing nonsingular inverse-congruence and secant-pair
compression identities; no orthogonality of the actual direction basis is assumed.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant
open scoped BigOperators Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Apply a linear change of form coordinates to every actual scenario operator.
Use: carry base, increments and both correction regimes through the same physical congruence.
Article: main_krylov, apD:centre, X̃=DᵀXD. -/
def Scenario.mapForms (S : Scenario p)
    (f : Matrix (Fin p) (Fin p) ℝ →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ) : Scenario p where
  base := f S.base
  increment := fun l => f (S.increment l)
  terminal := f S.terminal
  correction := fun k => f (S.correction k)

/-- The actual inverse congruence is linear on curvature forms.
Use: transport scenario sums and reflections without assuming a coordinate identity.
Article: main_krylov, thm:centre, X=D^(−T)X̃D^(−1).
Proof: fixed matrix multiplication is real-linear on both sides. -/
def inverseFormMap (D : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ where
  toFun := inverseCongruence D
  map_add' := by intro X Y; simp only [inverseCongruence,Matrix.mul_add,Matrix.add_mul]
  map_smul' := by intro c X; simp only [inverseCongruence,Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

/-- The scenario represented by actual physical operators in a chosen full direction basis.
Use: every exact reflection statement below concerns these real operators, not fictitious normalized probes.
Article: main_krylov, thm:centre, physical operators recovered from direction coordinates. -/
def Scenario.inPhysical (S : Scenario p) (D : Matrix (Fin p) (Fin p) ℝ) : Scenario p :=
  S.mapForms (inverseFormMap D)

/-- Linear transport commutes with every actual finite accumulated probe operator.
Use: a physical scenario's probes are precisely inverse congruences of the coordinate probes.
Article: main_krylov, apD:centre, coordinate transport of A_k.
Proof: apply linearity to the base and the finite sum of preceding increments. -/
theorem Scenario.mapForms_probe (S : Scenario p)
    (f : Matrix (Fin p) (Fin p) ℝ →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    (S.mapForms f).probe k=f (S.probe k) := by
  simp only [Scenario.probe,Scenario.mapForms,map_add,map_sum]

/-- Actual intermediate correction operators commute with the same physical form transport.
Use: compare their actions at genuine correction queries in the current physical span.
Article: main_krylov, thm:centre, coordinate transport of B_k.
Proof: both the current probe and the independent correction perturbation are transported linearly. -/
theorem Scenario.mapForms_intermediate (S : Scenario p)
    (f : Matrix (Fin p) (Fin p) ℝ →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    (S.mapForms f).intermediate k=f (S.intermediate k) := by
  change (S.mapForms f).probe k+f (S.correction k)=f (S.probe k+S.correction k)
  rw [Scenario.mapForms_probe,map_add]

/-- Actual terminal correction operators commute with physical form transport.
Use: the transported terminal pair is still the explicit operator pair of the scenario.
Article: main_krylov, thm:centre, coordinate transport of B_(n−1).
Proof: transport the accumulated probe and the final independent perturbation. -/
theorem Scenario.mapForms_lastOperator (S : Scenario p)
    (f : Matrix (Fin p) (Fin p) ℝ →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ) (N : ℕ) :
    (S.mapForms f).lastOperator N=f (S.lastOperator N) := by
  change (S.mapForms f).probe N+f S.terminal=f (S.probe N+S.terminal)
  rw [Scenario.mapForms_probe,map_add]

/-- Multiplying an inverse-congruent form by its actual basis cancels the right inverse.
Use: equality of coordinate columns becomes equality of full physical operator actions.
Article: main_krylov, thm:centre, A_k^♯d_k=A_kd_k.
Proof: reassociate the true nonsingular product and cancel D⁻¹D. -/
theorem inverseForm_mul_basis (D X : Matrix (Fin p) (Fin p) ℝ) (hD : IsUnit D.det) :
    inverseFormMap D X * D=Dᵀ⁻¹ * X := by
  change inverseCongruence D X*D=Dᵀ⁻¹*X
  simp only [inverseCongruence,Matrix.mul_assoc,nonsing_inv_mul _ hD,Matrix.mul_one]

/-- The reflected scenario preserves the physical action on every current direction column.
Use: the source's exact probe equality holds in arbitrary nonorthogonal physical coordinates.
Article: main_krylov, thm:centre, physical probe preservation.
Proof: cancel the actual basis in both inverse congruences, then use the proved
coordinate column equality in each summand of the left matrix product. -/
theorem Scenario.physical_reflect_probe_column (S : Scenario p)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : IsUnit D.det)
    {k N : ℕ} (hk : k ≤ N) (j : Fin p) (hj : j.val=k) (i : Fin p) :
    (((S.reflect N).inPhysical D).probe k*D) i j=
      ((S.inPhysical D).probe k*D) i j := by
  -- Cancel the actual right basis factor before comparing coordinate columns.
  simp only [Scenario.inPhysical,Scenario.mapForms_probe]
  rw [inverseForm_mul_basis D ((S.reflect N).probe k) hD,inverseForm_mul_basis D (S.probe k) hD]
  simp only [Matrix.mul_apply]
  apply sum_congr rfl
  intro a _
  rw [S.reflect_probe_column hk j hj a]

/-- Every physical intermediate correction column in the current direction prefix is preserved.
Use: exact oracle equality extends to all physical correction combinations in that prefix.
Article: main_krylov, thm:centre, B_k^♯=B_k on 𝒱_k.
Proof: use the actual inverse-congruence cancellation and the proved whole-prefix coordinate equality. -/
theorem Scenario.physical_reflect_intermediate_column (S : Scenario p)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : IsUnit D.det)
    {k N : ℕ} (hk : k ≤ N) (j : Fin p) (hj : j.val ≤ k) (i : Fin p) :
    (((S.reflect N).inPhysical D).intermediate k*D) i j=
      ((S.inPhysical D).intermediate k*D) i j := by
  -- Transfer the preserved whole-prefix coordinate actions to the real physical basis.
  simp only [Scenario.inPhysical,Scenario.mapForms_intermediate]
  rw [inverseForm_mul_basis D ((S.reflect N).intermediate k) hD,
    inverseForm_mul_basis D (S.intermediate k) hD]
  simp only [Matrix.mul_apply]
  apply sum_congr rfl
  intro a _
  rw [S.reflect_intermediate_column hk j hj a]

/-- The coordinate observations are exactly the actual physical direction/probe pairing data.
Use: the centre below is computable from the real measured probes and the actual directions.
Article: main_krylov, thm:centre, M_D=Dᵀ[z₀,…,z_(n−1)].
Proof: each physical compressed probe recovers its original coordinate form;
the existing observed-compression identity identifies its measured columns. -/
theorem Scenario.physical_observed_data (S : Scenario p)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : IsUnit D.det) :
    Dᵀ*pairImages D (S.inPhysical D).probe=observed S.probe := by
  -- Every actual compressed physical probe reconstructs its coordinate form exactly.
  rw [← observed_compression]
  congr 1
  funext k
  rw [Scenario.inPhysical,Scenario.mapForms_probe]
  exact compress_inverseCongruence D (S.probe k) hD

/-- The physical latest-information centre formed from genuine observed probe vectors.
Use: no unknown operator is exposed to the estimator of the terminal model.
Article: main_krylov, thm:centre, J_D=D^(−T)T_DD^(−1). -/
def Scenario.physicalCentre (S : Scenario p) (D : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  inverseCongruence D (latest (Dᵀ*pairImages D (S.inPhysical D).probe))

/-- The constructed physical twin terminal operator is reflected about the actual data-only physical model.
Use: tie the exact centre theorem to actual physical observations in a general full direction basis.
Article: main_krylov, thm:centre, B_(n−1)^♯=2J_D−B_(n−1).
Proof: apply the linear inverse-congruence map to the proved coordinate reflection
and identify the coordinate model with the genuine measured physical pairings. -/
theorem Scenario.physical_reflect_about_centre {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (hA : S.base.IsSymm) (hE : ∀ l, (S.increment l).IsSymm) :
    ((S.reflect N).inPhysical D).lastOperator N=
      (2 : ℝ) • S.physicalCentre D-(S.inPhysical D).lastOperator N := by
  -- Transport the constructed reflection linearly and recover the model from actual observations.
  simp only [Scenario.inPhysical,Scenario.mapForms_lastOperator,
    S.reflect_about_latest hA hE,map_sub,map_smul]
  unfold Scenario.physicalCentre
  rw [S.physical_observed_data D hD]
  rfl

end
end krylov.Information
