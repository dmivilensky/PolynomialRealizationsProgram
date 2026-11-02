import jacobi.Support.Parameters
import jacobi.Finite.Fiber

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The original uncorrected cosine lattice is a genuine strictly ordered
finite node family inside (-1,1). It therefore uses the earlier finite
spectral reconstruction and persymmetry theory without a second node type.
Use: naturalNodes and the actual support characteristic polynomial retain exactly the original finite lattice enumeration.
-/
namespace jacobi.Support
noncomputable section
open Real Set jacobi.Reference

/-- The original natural support cosine node at its unchanged zero-based index.
Use: naturalNodes and the actual support characteristic polynomial retain exactly the original finite lattice enumeration.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def naturalNode (a b : ℝ) (n k : ℕ) : ℝ := cos (jacobi.Jacobi.modelAngle a b n k)

/-- The original model angle is its genuine gamma lattice coordinate times the actual support step.
Use: endpoint Darboux deletion reindexes the original smaller lattice without any asymptotic replacement.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: insert the previously proved actual leading phase identity and the literal unchanged step. -/
theorem modelAngle_step (a b : ℝ) (n k : ℕ) :
    jacobi.Jacobi.modelAngle a b n k=((k:ℝ)+gamma a)*step a b n := by
  rw [jacobi.Jacobi.modelAngle,phaseGrid_eq,step]
  ring

/-- The genuine natural support cosine nodes lie strictly inside the original contractive interval at every nonempty index.
Use: naturalNodes feeds the existing finite fibre reconstruction and canonical persymmetric-weight theorem.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the actual original angles lie strictly between zero and pi; strict cosine monotonicity gives both endpoint margins. -/
theorem naturalNode_mem {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk:k<n) :
    naturalNode a b n k∈Ioo (-1:ℝ) 1 := by
  have ht := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb hk).1
  constructor
  · simpa only [Real.cos_pi,naturalNode] using Real.strictAntiOn_cos ⟨ht.1.le,ht.2.le⟩
      ⟨Real.pi_pos.le,le_rfl⟩ ht.2
  · simpa only [Real.cos_zero,naturalNode] using Real.strictAntiOn_cos ⟨le_rfl,Real.pi_pos.le⟩
      ⟨ht.1.le,ht.2.le⟩ ht.1

/-- The actual natural support cosine lattice is strictly decreasing in the article's original spectral order.
Use: naturalNodes supplies the earlier finite inverse-spectral construction with exactly the genuine original ordered lattice.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the original positive step makes the genuine angle lattice strictly increasing inside (0,pi), where cosine is strictly decreasing. -/
theorem naturalNode_strictAnti {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    StrictAnti (fun k:Fin n => naturalNode a b n k) := by
  intro i j hij
  have hi := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb i.isLt).1
  have hj := (jacobi.Jacobi.modelAngle_endpoint_bounds ha hb j.isLt).1
  apply Real.strictAntiOn_cos ⟨hi.1.le,hi.2.le⟩ ⟨hj.1.le,hj.2.le⟩
  rw [modelAngle_step,modelAngle_step]
  apply mul_lt_mul_of_pos_right _ (step_pos ha hb (by omega))
  have hh : (i:ℝ)<(j:ℝ) := by exact_mod_cast hij
  linarith

/-- The original natural support node family in the previously verified arbitrary-fibre interface.
Use: the exact original support spectrum and persymmetry identify its actual spectral weights with the existing reciprocal-derivative probabilities, which drive the finite Gram comparison.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def naturalNodes (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : jacobi.Finite.Nodes n where
  value k := naturalNode a b n k
  strictAnti := naturalNode_strictAnti ha hb n
  interval k := naturalNode_mem ha hb k.isLt

end
end jacobi.Support
