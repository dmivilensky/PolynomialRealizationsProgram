import krylov.Reference.FullCycle
import Mathlib.Analysis.Asymptotics.Lemmas
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine full-frame incoming reconstruction.
Use: true canonical CG coordinate remainders reconstruct the actual full
physical vector with the same original parameter order.
Source: mathlib orthonormal-basis completeness in the genuine finite
dimension, exact coordinate reconstruction and finite normed sums.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Filter Topology Asymptotics
open scoped InnerProductSpace BigOperators
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- Every actual finite coordinate bound in a genuine complete real
orthonormal frame reconstructs the true vector bound with the same order.
Use: canonical incoming rows imply the original full incoming gradient
formula, rather than an assertion only about selected coordinates.
Article: main_krylov, thm:local(a), genuine full CG-frame reconstruction.
Proof: true orthonormality gives independent vectors, and the actual
ambient dimension makes their span the whole space. The resulting real
orthonormal basis reconstructs each vector exactly. Bound each actual
coordinate times its fixed vector and sum the genuine finite family. -/
theorem full_orthonormal_frame_order
    (q : Fin n → EuclideanSpace ℝ (Fin n)) (ho : Orthonormal ℝ q)
    (v : α → EuclideanSpace ℝ (Fin n)) (s : α → ℝ)
    (hrows : ∀ i,(fun z => inner ℝ (q i) (v z)) =O[l] s) : v =O[l] s := by
  have hdim : Fintype.card (Fin n)=Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  have hspan : Submodule.span ℝ (Set.range q)=⊤ := ho.linearIndependent.span_eq_top_of_card_eq_finrank' hdim
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := OrthonormalBasis.mk ho hspan.ge
  have hbq (i : Fin n) : b i=q i := congrFun (OrthonormalBasis.coe_mk ho hspan.ge) i
  have hprod (i : Fin n) : (fun z => inner ℝ (q i) (v z) • q i) =O[l] s := by
    have hc : (fun _ : α => q i) =O[l] (fun _ => (1 : ℝ)) := tendsto_const_nhds.isBigO_one ℝ
    simpa only [mul_one,smul_eq_mul] using (hrows i).smul hc
  have hsum := IsBigO.sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => hprod i)
  apply hsum.congr_left
  intro z
  simp only [Finset.sum_apply]
  simpa only [hbq] using b.sum_repr' (v z)

end
end krylov.LinearAlgebra
