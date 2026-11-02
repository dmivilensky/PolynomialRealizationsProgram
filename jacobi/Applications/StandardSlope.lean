import jacobi.Applications.StandardJacobi
import jacobi.Jacobi.StandardSlopeMesh
import jacobi.Finite.FlowDerivatives

/-!
The actual standard-flow energy derivative and its continuum integral.
The initial matrix is the genuine standard Jacobi fibre member. The exact
Lax derivative is the same triangular Green mesh whose full dominated
limit was proved, so no spectral-weight or derivative-limit premise remains.
Use: StandardDescent evaluates this integral and combines the result with
the actual flow's Taylor estimate to obtain finite-fibre strict improvement.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
Article role: the limit of the actual initial finite-matrix energy derivative.
-/
namespace jacobi.Applications
noncomputable section
open Real Set Filter jacobi.Jacobi jacobi.Finite chebyshev2
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual standard matrix in its proved polynomial fibre.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
def standardFiber (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    jacobi.Finite.Fiber (n+1) (nodes a b ha hb (n+1)).polynomial :=
  ⟨standardChain a b ha hb (n+1),standardChain_inFiber ha hb (n+1)⟩

/-- The true initial derivative of the standard realization's energy
under the global resolvent flow, in its original unscaled units.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
def standardInitialVelocity (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : ℝ :=
  flowEnergyVelocity (nodes a b ha hb (n+1))
    (spectralWeights _ (standardFiber a b ha hb n)) 0

/-- The tail expression is the genuine Green entry in both triangles.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standardGreenTail_entry {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {N : ℕ} (i j : Fin N) :
    standardGreenTail a b N i j=(standardChain a b ha hb N).green i j := by
  rcases le_total i j with hij | hji
  · exact standardGreenTail_entry_of_le ha hb i j hij
  · have hs : standardGreenTail a b N i j=standardGreenTail a b N j i := by
      unfold standardGreenTail
      rw [max_comm]
      ring
    rw [hs,standardGreenTail_entry_of_le ha hb j i hji]
    exact (standardChain a b ha hb N).green_symmetric
      ((standardChain a b ha hb N).pencils_of_contractive
        ((nodes a b ha hb N).contractive (standardChain_inFiber ha hb N))).1 i j

/-- This declared velocity is an actual derivative of the actual
standard matrix flow energy, not a separately defined proxy derivative.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standardInitialVelocity_hasDerivAt {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    HasDerivAt (fun t : ℝ =>
      (resolventFlow (nodes a b ha hb (n+1)) (standardFiber a b ha hb n) t).val.energy)
      (standardInitialVelocity a b ha hb n) 0 := by
  convert flowEnergy_hasDerivAt (nodes a b ha hb (n+1))
    (spectralWeights _ (standardFiber a b ha hb n)) 0 using 1
  · funext t
    rw [flowEnergy_eq]
    rfl
  · rfl

/-- The genuine normalized initial derivative is exactly the genuine
double mesh, with both finite normalizations and every physical entry
identified before taking a limit.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standard_initial_slope_mesh_identity {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    standardInitialVelocity a b ha hb n/((n+1:ℕ):ℝ)^3=
      (∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1),
        standardSlopeSummand a b (n+1) i j)/((n+1:ℕ):ℝ)^2 := by
  let S := nodes a b ha hb (n+1)
  let J := standardFiber a b ha hb n
  have hg : flowGreen S (spectralWeights S J) 0=J.val.green := by
    rw [flowGreen_eq,resolventWeights_zero,reconstruct_spectralWeights]
  have hsum : (∑ i∈Finset.range (n+1),∑ j∈Finset.range (n+1),
      standardSlopeSummand a b (n+1) i j)=
        (4/((n+1:ℕ):ℝ)^3)*(∑ i:Fin (n+1),∑ j:Fin (n+1),if j < i then
          (J.val.green i i-J.val.green j j)*(J.val.green i j)^2 else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j∈Finset.range (n+1),
      standardSlopeSummand a b (n+1) i j) (n+1),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => standardSlopeSummand a b (n+1) i j) (n+1),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold standardSlopeSummand
    simp only [Fin.lt_def]
    split_ifs
    · rw [standardGreenTail_entry ha hb i i,standardGreenTail_entry ha hb j j,
        standardGreenTail_entry ha hb i j]
      change 4*((standardChain a b ha hb (n+1)).green i i/((n+1:ℕ):ℝ)-
        (standardChain a b ha hb (n+1)).green j j/((n+1:ℕ):ℝ))*
          ((standardChain a b ha hb (n+1)).green i j/((n+1:ℕ):ℝ))^2=_
      dsimp [J,standardFiber]
      field_simp
    · simp only [mul_zero]
  rw [hsum,standardInitialVelocity,flowEnergyVelocity_pairs]
  change (4*flowScale (n+1)*(∑ i,∑ j,if j < i then
      (flowGreen S (spectralWeights S J) 0 i i-flowGreen S (spectralWeights S J) 0 j j)*
        (flowGreen S (spectralWeights S J) 0 i j)^2 else 0))/((n+1:ℕ):ℝ)^3=_
  rw [hg,flowScale]
  push_cast
  ring

/-- The actual normalized initial derivative has its full one-sided
Green-pair integral limit, with all finite, spectral and corner estimates
discharged by the preceding exact constructions.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standard_initial_slope_integral_limit {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => standardInitialVelocity a b (by linarith : -1<a) hb n/
      ((n+1:ℕ):ℝ)^3) atTop (𝓝 (standardSlopeIntegral a)) := by
  have ha' : -1<a := by linarith
  simp_rw [standard_initial_slope_mesh_identity ha' hb]
  exact (standardSlope_mesh_integral_limit ha hb).comp (tendsto_add_atTop_nat 1)

end
end jacobi.Applications
