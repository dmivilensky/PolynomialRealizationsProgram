import krylov.Secant.ModelError

/-!
Article: main_krylov, apG:mss, physical/normalized column bridge.
Use: connect the actual positive-root normalized physical observations and MSS
model to the actual unit-column model-error calculus.
Source: genuine metric-root cancellation and the proved latest-information observation formula.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- Physical column energies computed from the actual positive metric root.
Use: supplies the actual diagonal N rather than assumed column-normalization data.
Article: main_krylov, apG:mss, N_ii=‖u_i‖_A. -/
def columnEnergies (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Fin (n+1) → ℝ :=
  fun i => ‖euclideanColumn (metricRoot base*U) i‖

/-- Actual normalized physical columns in the genuine canonical metric.
Use: the conditioning and oldest-distance theorems apply to these actual observations.
Article: main_krylov, apG:mss, Û=A^(1/2)UN⁻¹. -/
def normalizedColumns (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  metricRoot base*U*diagonal (fun i => (columnEnergies base U i)⁻¹)

/-- Every actual physical reference column has positive energy in a positive metric.
Use: justify the actual normalizer N before inversion or unit-column estimates.
Article: main_krylov, apG:mss, positive normalized column energies.
Proof: root times U is actually invertible, so its linearly independent actual
columns are nonzero; their genuine Euclidean norms are strictly positive. -/
theorem columnEnergies_pos (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det) (i : Fin (n+1)) : 0<columnEnergies base U i := by
  -- Invertibility makes each actual column nonzero before taking its Euclidean norm.
  have hu : IsUnit (metricRoot base*U).det := by
    rw [det_mul]
    exact (metricRoot_det_unit base hbase).mul hU
  have hc := (Matrix.linearIndependent_cols_of_det_ne_zero ((isUnit_iff_ne_zero.mp hu))).ne_zero i
  apply norm_pos_iff.mpr
  intro hz
  apply hc
  funext a
  exact congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => v a) hz

/-- The actual inverse-energy diagonal is nonsingular.
Use: the normalized observation window remains a genuine full basis.
Article: main_krylov, apG:mss, N⁻¹ exists.
Proof: its actual determinant is the product of nonzero positive-energy reciprocals. -/
theorem inverse_energy_diagonal_unit (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det) :
    IsUnit (diagonal (fun i => (columnEnergies base U i)⁻¹)).det := by
  rw [det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (columnEnergies_pos base U hbase hU i).ne'

/-- The actual canonical normalized column matrix is invertible.
Use: all actual least-gain and oldest-distance conclusions have their required genuine domain.
Article: main_krylov, apG:mss, Û invertible.
Proof: multiply the three actual nonsingular factors. -/
theorem normalizedColumns_unit (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det) : IsUnit (normalizedColumns base U).det := by
  rw [normalizedColumns, det_mul, det_mul]
  exact ((metricRoot_det_unit base hbase).mul hU).mul (inverse_energy_diagonal_unit base U hbase hU)

/-- The actual canonical normalized physical columns have genuine Euclidean norm one.
Use: discharges the unit-column hypothesis of the actual n-times model-error estimate.
Article: main_krylov, apG:mss, ‖û_i‖=1.
Proof: each actual diagonal multiplication divides its actual column by its positive energy. -/
theorem normalizedColumns_norm (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det) (i : Fin (n+1)) :
    ‖euclideanColumn (normalizedColumns base U) i‖=1 := by
  -- Identify the actual scaled column first, then use its proved positive normalizer.
  have he : euclideanColumn (normalizedColumns base U) i=
      (columnEnergies base U i)⁻¹ • euclideanColumn (metricRoot base*U) i := by
    ext a
    simp only [euclideanColumn, normalizedColumns, mul_diagonal, PiLp.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (columnEnergies_pos base U hbase hU i).le)]
  exact inv_mul_cancel₀ (columnEnergies_pos base U hbase hU i).ne'

/-- Latest-information symmetrization commutes with an actual real diagonal congruence.
Use: normalize the actual observation matrix without changing its newer-column convention.
Article: main_krylov, apG:mss, N⁻¹HN⁻¹.
Proof: choose the actual upper triangle; swapping the lower indices only swaps commuting real factors. -/
theorem latest_diagonal_congruence (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    latest (diagonal d*M*diagonal d)=diagonal d*latest M*diagonal d := by
  ext i j
  simp only [latest, diagonal_mul, mul_diagonal]
  rcases le_total i j with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]
    ring

/-- Actual physical compressed forms equal actual normalized canonical compressed forms after scaling.
Use: the metric root and both actual inverse roots cancel inside every observed column.
Article: main_krylov, apG:mss, physical normalized data bridge.
Proof: transpose the actual column product, cancel each genuine metric root
against its inverse, and retain the actual diagonal scaling on both exterior sides. -/
theorem normalized_columns_compression (base U A : Matrix (Fin n) (Fin n) ℝ)
    (hbase : base.PosDef) (d : Fin n → ℝ) :
    (metricRoot base*U*diagonal d)ᵀ*relativeOperator base A*(metricRoot base*U*diagonal d)=
      diagonal d*(Uᵀ*A*U)*diagonal d := by
  -- Cancel the adjacent genuine root/inverse-root pairs while preserving all physical factors.
  have hR := metricRoot_det_unit base hbase
  simp only [transpose_mul, diagonal_transpose, (metricRoot_isSymm base).eq, relativeOperator]
  calc
    _ = diagonal d*Uᵀ*(metricRoot base*(metricRoot base)⁻¹)*A*
        ((metricRoot base)⁻¹*metricRoot base)*U*diagonal d := by noncomm_ring
    _ = _ := by rw [mul_nonsing_inv _ hR, nonsing_inv_mul _ hR]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- The actual normalized physical observations give exactly the scaled actual physical latest model.
Use: links the physical H and the genuine normalized data used in the error estimate.
Article: main_krylov, apG:mss, Ĥ=N⁻¹HN⁻¹.
Proof: apply the proved true compressed identity at each actual observed column
and then the proved diagonal covariance of latest-information symmetrization. -/
theorem normalized_latest_model (base U : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    latest ((metricRoot base*U*diagonal d)ᵀ*pairImages (metricRoot base*U*diagonal d)
      (fun k => relativeOperator base (A k))) = diagonal d*latest (Uᵀ*pairImages U A)*diagonal d := by
  -- The same actual compression identity applies at every column's own observation time.
  have he : (metricRoot base*U*diagonal d)ᵀ*pairImages (metricRoot base*U*diagonal d)
      (fun k => relativeOperator base (A k)) = diagonal d*(Uᵀ*pairImages U A)*diagonal d := by
    rw [← observed_compression, ← observed_compression]
    ext i j
    change ((metricRoot base*U*diagonal d)ᵀ*relativeOperator base (A j.val)*
      (metricRoot base*U*diagonal d)) i j=_
    rw [normalized_columns_compression base U _ hbase d]
    simp only [diagonal_mul, mul_diagonal, observed]
  rw [he, latest_diagonal_congruence]

/-- An actual diagonal rescaling of a physical model has exactly the same actual canonical ambient model.
Use: identifies the normalized latest-observation model with the true physical MSS matrix J.
Article: main_krylov, apG:mss, Ĵ=A^(−1/2)JA^(−1/2).
Proof: compress the actual physical inverse-congruence model by U times the
diagonal, recover the actual scaled H, and apply the proved metric-step cancellation. -/
theorem normalized_inverse_model (base U H : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsUnit U.det) (d : Fin n → ℝ) (hd : IsUnit (diagonal d).det) :
    inverseCongruence (metricRoot base*U*diagonal d) (diagonal d*H*diagonal d)=
      relativeOperator base (inverseCongruence U H) := by
  -- Recover the actual scaled window form by direct compression of the physical model.
  have hS : IsUnit (U*diagonal d).det := by rw [det_mul]; exact hU.mul hd
  have he : (U*diagonal d)ᵀ*inverseCongruence U H*(U*diagonal d)=diagonal d*H*diagonal d := by
    rw [transpose_mul, diagonal_transpose]
    calc
      _ = diagonal d*(Uᵀ*inverseCongruence U H*U)*diagonal d := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [compress_inverseCongruence U H hU]
  have hc := inverseCongruence_metric base (inverseCongruence U H) (U*diagonal d) hS
  rw [he] at hc
  simpa only [Matrix.mul_assoc] using hc

/-- The actual normalized data give the complete actual physical MSS error identity.
Use: discharges the canonical/physical bridge for the source's normalized model formula.
Article: main_krylov, apG:mss, first displayed identity for Ĵ−I.
Proof: actual positive column energies give a nonsingular normalized basis;
its actual latest model is the actual scaled physical H, whose inverse congruence
is exactly the physical canonical model by the proved cancellation theorem. -/
theorem physical_normalized_model_error (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det)
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    relativeOperator base (inverseCongruence U (latest (Uᵀ*pairImages U A)))-1 =
      inverseCongruence (normalizedColumns base U)
        (normalizedDataError (normalizedColumns base U) (fun k => relativeOperator base (A k))) := by
  have he := normalized_model_error (normalizedColumns base U) (normalizedColumns_unit base U hbase hU)
    (fun k => relativeOperator base (A k))
  rw [normalizedColumns, normalized_latest_model base U hbase A,
    normalized_inverse_model base U _ hU _ (inverse_energy_diagonal_unit base U hbase hU)] at he
  exact he

/-- The printed uniform physical MSS error bound holds for the actual normalized physical columns.
Use: no column normalizer, inverse domain or physical/canonical identification remains assumed.
Article: main_krylov, apG:mss, complete dimension/conditioning bound.
Proof: apply the proved actual normalized estimate with the actual positive-root
normalized columns, their proved unit norms and the actual relative segment operators. -/
theorem physical_normalized_model_bound (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det)
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : ∀ k, (A k).IsSymm)
    {ε : ℝ} (hε : 0≤ε) (hbudget : ∀ k<n+1, ‖relativeOperator base (A k)-1‖≤ε) :
    ‖relativeOperator base (inverseCongruence U (latest (Uᵀ*pairImages U A)))-1‖≤
      (n+1)*ε/(leastGain (normalizedColumns base U))^2 := by
  have he := normalized_model_bound (normalizedColumns base U) (normalizedColumns_unit base U hbase hU)
    (fun k => relativeOperator base (A k)) (fun k => relativeOperator_isSymm base (A k) (hA k))
    (normalizedColumns_norm base U hbase hU) hε hbudget
  rw [normalizedColumns, normalized_latest_model base U hbase A,
    normalized_inverse_model base U _ hU _ (inverse_energy_diagonal_unit base U hbase hU)] at he
  exact he

/-- Adding an actual physical symmetric-data correction changes the true normalized X by its actual N⁻¹DN⁻¹.
Use: every identity and conditioning estimate applies to the actual corrected MSS model as well.
Article: main_krylov, apG:mss, corrected X_D.
Proof: distribute both actual congruences over addition and use the proved physical identity. -/
theorem physical_corrected_model_error (base U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbase : base.PosDef) (hU : IsUnit U.det)
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    let Ninv := diagonal (fun i => (columnEnergies base U i)⁻¹)
    relativeOperator base (inverseCongruence U (latest (Uᵀ*pairImages U A)+D))-1 =
      inverseCongruence (normalizedColumns base U)
        (normalizedDataError (normalizedColumns base U) (fun k => relativeOperator base (A k))+Ninv*D*Ninv) := by
  -- The correction contributes linearly through exactly the same actual diagonal congruence.
  dsimp only
  have hd := normalized_inverse_model base U D hU _ (inverse_energy_diagonal_unit base U hbase hU)
  have he := physical_normalized_model_error base U hbase hU A
  simp only [normalizedColumns, inverseCongruence, relativeOperator, Matrix.mul_add, Matrix.add_mul] at he hd ⊢
  rw [hd]
  rw [← he]
  abel

end
end krylov.Secant
