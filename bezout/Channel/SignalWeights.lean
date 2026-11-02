import bezout.Channel.SignalAlgebra
import bezout.Comparisons.Competitors.Endpoints

/-!
Article: bezout, Equation `eq:experiment-endpoint-transfer`.
Use: arbitrary signal mass on the two spectral endpoints controls the actual
channel operator norm and HS energy for Prefix, sine--Jacobi and Balanced.
Proof: their common endpoint time direction makes the endpoint block rank one;
orthogonal row masks and the full spectral maximum control the remaining rows.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J]

/-- A signal block with one common temporal direction. -/
def outerMatrix (b : J → ℝ) (u : Fin N → ℝ) : Matrix J (Fin N) ℝ := fun j s => b j*u s

/-- The actual rectangular map of a common temporal direction is rank one. -/
theorem outerMatrix_operator (b : J → ℝ) (u : Fin N → ℝ) :
    rectangularOperator (outerMatrix b u)=InnerProductSpace.rankOne ℝ
      (WithLp.toLp 2 b) (WithLp.toLp 2 u) := by
  apply ContinuousLinearMap.ext
  intro e
  ext j
  simp only [rectangularOperator_apply,outerMatrix,InnerProductSpace.rankOne_apply,
    PiLp.smul_apply,smul_eq_mul,PiLp.inner_apply,Real.inner_apply,
    Finset.sum_mul]
  
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The rank-one signal block attains all of its HS energy as operator energy. -/
theorem outerMatrix_norm_sq (b : J → ℝ) (u : Fin N → ℝ) :
    rectangularNorm (outerMatrix b u)^2=(∑ j, b j^2)*(∑ s, u s^2) := by
  rw [rectangularNorm,outerMatrix_operator,InnerProductSpace.norm_rankOne,mul_pow]
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]

/-- Exact squared HS energy of a rank-one endpoint block. -/
theorem outerMatrix_hsSq (b : J → ℝ) (u : Fin N → ℝ) :
    rectangularHsSq (outerMatrix b u)=(∑ j, b j^2)*(∑ s, u s^2) := by
  simp only [rectangularHsSq,outerMatrix,mul_pow,← Finset.mul_sum,← Finset.sum_mul]

variable [DecidableEq J]

/-- The endpoint part of a signal, retaining its signed physical amplitudes. -/
def endpointAmplitudes (I : chebyshev1.SpectralInterval) (lam a : J → ℝ)
    (F : Finset J) (σ : ℝ) (j : J) : ℝ :=
  if j∈F then a j*(if lam j=I.mu then 1 else σ) else 0

/-- Endpoint signal mass, without any restriction to an experimental weight. -/
def endpointMass (F : Finset J) (a : J → ℝ) : ℝ := ∑ j∈F, a j^2

omit [Fintype J] in
/-- Actual endpoint parity turns the retained physical signal matrix into rank one. -/
theorem signal_endpoint_block (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (lam a : J → ℝ) (F : Finset J) (σ : ℝ)
    (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L)
    (hp : ∀ s, bezout.Lower.physicalKernel h s I.L I.L=
      σ*bezout.Lower.physicalKernel h s I.mu I.mu) :
    rowMask F (signalMatrix h lam a)=outerMatrix (endpointAmplitudes I lam a F σ)
      (fun s => bezout.Lower.physicalKernel h s I.mu I.mu) := by
  ext j s
  by_cases hj : j∈F
  · rcases hF j hj with hm|hL
    · simp [rowMask,signalMatrix,outerMatrix,endpointAmplitudes,hj,hm]
    · have hLm : I.L≠I.mu := I.mu_lt_L.ne'
      simp [rowMask,signalMatrix,outerMatrix,endpointAmplitudes,hj,hL,hLm,hp,mul_assoc]
  · simp [rowMask,outerMatrix,endpointAmplitudes,hj]

/-- A common endpoint sign of modulus one preserves all endpoint mass. -/
theorem endpointAmplitudes_energy (I : chebyshev1.SpectralInterval) (lam a : J → ℝ)
    (F : Finset J) (σ : ℝ) (hσ : σ^2=1) :
    (∑ j, endpointAmplitudes I lam a F σ j^2)=endpointMass F a := by
  calc
    _ = ∑ j, if j∈F then a j^2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j∈F
      · by_cases he : lam j=I.mu <;> simp [endpointAmplitudes,hj,he,mul_pow,hσ]
      · simp [endpointAmplitudes,hj]
    _ = _ := by simp [endpointMass]

omit [DecidableEq J] in
/-- A unit signal has full HS energy at most the squared spectral maximum. -/
theorem signal_hsSq_le_gain_sq (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (lam a : J → ℝ) (hlam : ∀ j, lam j∈Set.Icc I.mu I.L) (ha : ∑ j, a j^2=1) :
    rectangularHsSq (signalMatrix h lam a)≤h.spectralGain I^2 := by
  have hrow (j : J) : bezout.Lower.physicalKernelSq h (lam j) (lam j)≤h.spectralGain I^2 := by
    have hb := h.physical_kernelNorm_le_gain I (hlam j) (hlam j)
    have hs := Real.sq_sqrt (bezout.Lower.physicalKernelSq_nonneg h (lam j) (lam j))
    have hpos : 0≤h.spectralGain I := (Real.sqrt_nonneg _).trans hb
    nlinarith [Real.sqrt_nonneg (bezout.Lower.physicalKernelSq h (lam j) (lam j))]
  calc
    _ = ∑ j, a j^2*bezout.Lower.physicalKernelSq h (lam j) (lam j) := by
      simp only [rectangularHsSq,signalMatrix,mul_pow,← Finset.mul_sum]
      rfl
    _ ≤ ∑ j, a j^2*h.spectralGain I^2 :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul,ha,one_mul]

/-- General endpoint-mass transfer for an actual history with a common endpoint
profile and endpoint-attained spectral maximum. Both gain notions retain at
least the endpoint mass fraction of the squared spectral gain. -/
theorem signal_endpoint_mass_bounds (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (lam a : J → ℝ) (F : Finset J) (σ : ℝ) (hσ : σ^2=1)
    (hlam : ∀ j, lam j∈Set.Icc I.mu I.L) (ha : ∑ j, a j^2=1)
    (hF : ∀ j∈F, lam j=I.mu ∨ lam j=I.L)
    (hp : ∀ s, bezout.Lower.physicalKernel h s I.L I.L=
      σ*bezout.Lower.physicalKernel h s I.mu I.mu)
    (hg : h.spectralGain I=Real.sqrt (bezout.Lower.physicalKernelSq h I.mu I.mu)) :
    endpointMass F a*h.spectralGain I^2≤rectangularNorm (signalMatrix h lam a)^2 ∧
      rectangularNorm (signalMatrix h lam a)^2≤rectangularHsSq (signalMatrix h lam a) ∧
      rectangularHsSq (signalMatrix h lam a)≤h.spectralGain I^2 := by
  have he : rectangularNorm (rowMask F (signalMatrix h lam a))^2=
      endpointMass F a*h.spectralGain I^2 := by
    rw [signal_endpoint_block h I lam a F σ hF hp,outerMatrix_norm_sq,
      endpointAmplitudes_energy I lam a F σ hσ,hg,
      Real.sq_sqrt (bezout.Lower.physicalKernelSq_nonneg h I.mu I.mu)]
    rfl
  refine ⟨?_,rectangularNorm_sq_le_hsSq _,signal_hsSq_le_gain_sq h I lam a hlam ha⟩
  rw [← he]
  exact (rowMask_norm_sq_sandwich F (signalMatrix h lam a)).1

end
end bezout.Channel
