import bezout.Comparisons.RootAsymptotics.Profiles
import bezout.Channel.SignalSelectedRows

/-!
Article: bezout, Proposition D.1, arbitrary finite endpoint-plus-bulk signals.
Use: replaces the numerical network weights by two arbitrary equal positive
endpoint mode energies and any finite collection of fixed interior modes.
All matrices below are physical first-variation matrices of actual histories.
Proof: exact endpoint Gram coefficients and explicit finite bulk-energy bounds.
-/

namespace bezout.Comparisons.RootAsymptotics
noncomputable section
open scoped BigOperators
open Channel

/-- A finite physical spectrum with equal positive endpoint mode energies. -/
structure FiniteSignal (I : chebyshev1.SpectralInterval) (J : Type*) where
  eigenvalue : J → ℝ
  amplitude : J → ℝ
  lower : J
  upper : J
  distinct : lower≠upper
  lower_value : eigenvalue lower=I.mu
  upper_value : eigenvalue upper=I.L
  mass : ℝ
  mass_pos : 0<mass
  lower_mass : amplitude lower^2=mass
  upper_mass : amplitude upper^2=mass
  interior : ∀ j, j≠lower → j≠upper → |I.z (eigenvalue j)|<1

variable {I : chebyshev1.SpectralInterval} {J : Type*} [Fintype J] [DecidableEq J]

/-- The physical LF/root channel matrix, for any actual ordering of the roots. -/
def rootMatrix (S : FiniteSignal I J) (N : ℕ) (e : Equiv.Perm (Fin N)) : Matrix J (Fin N) ℝ :=
  signalMatrix (Roots.history (Roots.steps I N e)) S.eigenvalue S.amplitude

/-- The physical Prefix channel matrix for the same spectrum and initial signal. -/
def prefixMatrix (S : FiniteSignal I J) (N : ℕ) : Matrix J (Fin N) ℝ :=
  signalMatrix (Classical.history I N) S.eigenvalue S.amplitude

/-- Explicit root bulk constant with all finite mode energies retained. -/
def rootBulkConstant (S : FiniteSignal I J) : ℝ :=
  ∑ j∈({S.lower,S.upper}:Finset J)ᶜ,
    S.amplitude j^2*Roots.interiorConstant (I.z (S.eigenvalue j))

/-- Explicit Prefix bulk constant with all finite mode energies retained. -/
def prefixBulkConstant (S : FiniteSignal I J) : ℝ :=
  ∑ j∈({S.lower,S.upper}:Finset J)ᶜ,
    S.amplitude j^2*prefixInteriorConstant (I.z (S.eigenvalue j))

omit [Fintype J] [DecidableEq J] in
/-- Equal endpoint energies imply an exact absolute amplitude product. -/
theorem endpoint_amplitude_product (S : FiniteSignal I J) :
    |S.amplitude S.lower*S.amplitude S.upper|=S.mass := by
  apply (sq_eq_sq₀ (abs_nonneg _) S.mass_pos.le).mp
  rw [sq_abs,mul_pow,S.lower_mass,S.upper_mass,pow_two]

omit [Fintype J] [DecidableEq J] in
/-- A physical signal row has its mode energy times the complete physical kernel energy. -/
theorem signal_row_energy {N : ℕ} (h : bezout.History N) (lam a : J → ℝ) (j : J) :
    temporalDot (signalMatrix h lam a j) (signalMatrix h lam a j)=
      a j^2*Lower.physicalKernelSq h (lam j) (lam j) := by
  unfold signalMatrix
  rw [temporalDot_scale]
  simp only [temporalDot,Lower.physicalKernelSq,pow_two,mul_assoc]

/-- The bulk HS energy is the finite sum of its genuine physical mode energies. -/
theorem signal_bulk_energy {N : ℕ} (h : bezout.History N) (lam a : J → ℝ)
    (F : Finset J) :
    rectangularHsSq (rowMask F (signalMatrix h lam a))=
      ∑ j∈F,a j^2*Lower.physicalKernelSq h (lam j) (lam j) := by
  calc
    _ = ∑ j,if j∈F then a j^2*Lower.physicalKernelSq h (lam j) (lam j) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j∈F
      · simp only [rowMask,hj,ite_true]
        exact (temporalDot_self _).symm.trans (signal_row_energy h lam a j)
      · simp [rowMask,hj]
    _ = _ := by simp

/-- Every root bulk mode is controlled by the same explicit finite quadratic constant. -/
theorem root_bulk_energy_le (S : FiniteSignal I J) (N : ℕ) (e : Equiv.Perm (Fin N)) :
    rectangularHsSq (rowMask ({S.lower,S.upper}ᶜ) (rootMatrix S N e))≤
      scaleSq I N*rootBulkConstant S*(N:ℝ)^2 := by
  rw [rootMatrix,signal_bulk_energy]
  unfold rootBulkConstant
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j≠S.lower ∧ j≠S.upper := by simpa using hj
  have hb := root_interior_energy I N e (S.interior j hj'.1 hj'.2)
  calc
    _ ≤ S.amplitude j^2*(scaleSq I N*Roots.interiorConstant (I.z (S.eigenvalue j))*(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

/-- Every Prefix bulk mode is controlled by the same explicit finite linear constant. -/
theorem prefix_bulk_energy_le (S : FiniteSignal I J) (N : ℕ) (hN : 0<N) :
    rectangularHsSq (rowMask ({S.lower,S.upper}ᶜ) (prefixMatrix S N))≤
      scaleSq I N*prefixBulkConstant S*(N:ℝ) := by
  rw [prefixMatrix,signal_bulk_energy]
  unfold prefixBulkConstant
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j≠S.lower ∧ j≠S.upper := by simpa using hj
  have hb := prefix_interior_energy I N hN (S.interior j hj'.1 hj'.2)
  calc
    _ ≤ S.amplitude j^2*(scaleSq I N*prefixInteriorConstant (I.z (S.eigenvalue j))*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

omit [Fintype J] [DecidableEq J] in
/-- The two exact root endpoint energies, as weighted physical matrix rows. -/
theorem root_endpoint_rows (S : FiniteSignal I J) (N : ℕ) (hEven : Even N)
    (e : Equiv.Perm (Fin N)) :
    temporalDot (rootMatrix S N e S.lower) (rootMatrix S N e S.lower)=
      S.mass*scaleSq I N*((2*(N:ℝ)^4+(N:ℝ)^2)/3) ∧
    temporalDot (rootMatrix S N e S.upper) (rootMatrix S N e S.upper)=
      S.mass*scaleSq I N*((2*(N:ℝ)^4+(N:ℝ)^2)/3) := by
  constructor
  · rw [rootMatrix,signal_row_energy,S.lower_value,S.lower_mass,Roots.history_endpointEnergy_mu]
    simp only [scaleSq,mul_assoc]
  · rw [rootMatrix,signal_row_energy,S.upper_value,S.upper_mass,
      Roots.history_endpointEnergy_L I N hEven]
    simp only [scaleSq,mul_assoc]

omit [Fintype J] [DecidableEq J] in
/-- Exact absolute endpoint cross coefficient of the actual root channel matrix. -/
theorem root_endpoint_cross (S : FiniteSignal I J) (N : ℕ) (hEven : Even N)
    (e : Equiv.Perm (Fin N)) :
    |temporalDot (rootMatrix S N e S.lower) (rootMatrix S N e S.upper)|=
      S.mass*scaleSq I N*(N:ℝ)^2 := by
  unfold rootMatrix signalMatrix
  rw [temporalDot_scale,S.lower_value,S.upper_value]
  change |S.amplitude S.lower*S.amplitude S.upper*
    (∑ s : Fin N,Lower.physicalKernel _ s I.mu I.mu*Lower.physicalKernel _ s I.L I.L)|=_
  rw [Roots.history_endpointCross I N hEven,abs_mul,endpoint_amplitude_product,
    abs_mul,abs_neg,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sq_nonneg _)]
  simp only [scaleSq,mul_assoc]

omit [Fintype J] [DecidableEq J] in
/-- Exact Prefix endpoint row energies and cross coefficient at every positive even horizon. -/
theorem prefix_endpoint_rows (S : FiniteSignal I J) (N : ℕ) (hN : 0<N) (hEven : Even N) :
    temporalDot (prefixMatrix S N S.lower) (prefixMatrix S N S.lower)=
      S.mass*scaleSq I N*chebyshev1.Prefix.shape N ∧
    temporalDot (prefixMatrix S N S.upper) (prefixMatrix S N S.upper)=
      S.mass*scaleSq I N*chebyshev1.Prefix.shape N ∧
    |temporalDot (prefixMatrix S N S.lower) (prefixMatrix S N S.upper)|=
      S.mass*scaleSq I N*chebyshev1.Prefix.shape N := by
  have he := prefix_endpoint_energy I N hN
  have hn := chebyshev1.Prefix.shape_nonneg N (by omega)
  have hrows : (fun s => Lower.physicalKernel (Classical.history I N) s I.L I.L)=
      fun s => -Lower.physicalKernel (Classical.history I N) s I.mu I.mu := by
    funext s
    exact prefix_endpoint_neg I N hN hEven s
  have hself : temporalDot (fun s => Lower.physicalKernel (Classical.history I N) s I.L I.L)
      (fun s => Lower.physicalKernel (Classical.history I N) s I.L I.L)=
      Lower.physicalKernelSq (Classical.history I N) I.mu I.mu := by
    rw [hrows,temporalDot_self]
    simp only [neg_sq]
    rfl
  have hself' : Lower.physicalKernelSq (Classical.history I N) I.L I.L=
      Lower.physicalKernelSq (Classical.history I N) I.mu I.mu := by
    simpa only [temporalDot_self,Lower.physicalKernelSq] using hself
  refine ⟨?_,?_,?_⟩
  · rw [prefixMatrix,signal_row_energy,S.lower_value,S.lower_mass,he]
    ring
  · rw [prefixMatrix,signal_row_energy,S.upper_value,S.upper_mass]
    rw [hself',he]
    ring
  · unfold prefixMatrix signalMatrix
    rw [temporalDot_scale,S.lower_value,S.upper_value,hrows]
    have hc : temporalDot (fun s => Lower.physicalKernel (Classical.history I N) s I.mu I.mu)
      (fun s => -Lower.physicalKernel (Classical.history I N) s I.mu I.mu)=
        -Lower.physicalKernelSq (Classical.history I N) I.mu I.mu := by
      simp only [temporalDot,Lower.physicalKernelSq,mul_neg,← Finset.sum_neg_distrib,pow_two]
    rw [hc,he,abs_mul,endpoint_amplitude_product,abs_neg,
      abs_of_nonneg (mul_nonneg (scaleSq_pos I N).le hn)]
    ring

/-- Actual root operator and HS energies have exact endpoint terms and a lower-order finite bulk. -/
theorem root_matrix_bounds (S : FiniteSignal I J) (N : ℕ) (hEven : Even N)
    (e : Equiv.Perm (Fin N)) :
    (S.mass*scaleSq I N*((2*(N:ℝ)^4+4*(N:ℝ)^2)/3)≤rectangularNorm (rootMatrix S N e)^2 ∧
      rectangularNorm (rootMatrix S N e)^2≤
        S.mass*scaleSq I N*((2*(N:ℝ)^4+4*(N:ℝ)^2)/3)+
          scaleSq I N*rootBulkConstant S*(N:ℝ)^2) ∧
    (S.mass*scaleSq I N*((4*(N:ℝ)^4+2*(N:ℝ)^2)/3)≤rectangularHsSq (rootMatrix S N e) ∧
      rectangularHsSq (rootMatrix S N e)≤
        S.mass*scaleSq I N*((4*(N:ℝ)^4+2*(N:ℝ)^2)/3)+
          scaleSq I N*rootBulkConstant S*(N:ℝ)^2) := by
  have hr := root_endpoint_rows S N hEven e
  have hs := selectedRows_equalEnergy_sandwich (rootMatrix S N e) S.lower S.upper S.distinct
    _ hr.1 hr.2
  rw [root_endpoint_cross S N hEven] at hs
  have hb := root_bulk_energy_le S N e
  have hz := rectangularHsSq_nonneg (rowMask ({S.lower,S.upper}ᶜ) (rootMatrix S N e))
  constructor <;> constructor <;> nlinarith [hs.1.1,hs.1.2,hs.2]

/-- Actual Prefix operator and HS energies share their endpoint leading term. -/
theorem prefix_matrix_bounds (S : FiniteSignal I J) (N : ℕ) (hN : 0<N) (hEven : Even N) :
    (2*S.mass*scaleSq I N*chebyshev1.Prefix.shape N≤rectangularNorm (prefixMatrix S N)^2 ∧
      rectangularNorm (prefixMatrix S N)^2≤2*S.mass*scaleSq I N*chebyshev1.Prefix.shape N+
        scaleSq I N*prefixBulkConstant S*(N:ℝ)) ∧
    (2*S.mass*scaleSq I N*chebyshev1.Prefix.shape N≤rectangularHsSq (prefixMatrix S N) ∧
      rectangularHsSq (prefixMatrix S N)≤2*S.mass*scaleSq I N*chebyshev1.Prefix.shape N+
        scaleSq I N*prefixBulkConstant S*(N:ℝ)) := by
  have hr := prefix_endpoint_rows S N hN hEven
  have hs := selectedRows_equalEnergy_sandwich (prefixMatrix S N) S.lower S.upper S.distinct
    _ hr.1 hr.2.1
  rw [hr.2.2] at hs
  have hb := prefix_bulk_energy_le S N hN
  have hz := rectangularHsSq_nonneg (rowMask ({S.lower,S.upper}ᶜ) (prefixMatrix S N))
  constructor <;> constructor <;> nlinarith [hs.1.1,hs.1.2,hs.2]

end
end bezout.Comparisons.RootAsymptotics
