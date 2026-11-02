import krylov.Methods.XRFC
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
Article: main_krylov, apA:prop:short, step-basis first-deletion obstruction.
Use: prove the general nonzero bidiagonal span obstruction used by the actual
short-window XRFC counterexample, rather than only a low-dimensional example.
Source: back substitution in the article; equivalently, an annihilating linear form.
-/

namespace krylov.Methods
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Every prescribed scalar family on linearly independent vectors extends to a linear form on the physical space.
Use: construct the actual annihilator of a retained bidiagonal step window.
Article: main_krylov, apA:prop:short, back-substitution functional.
Source: mathlib LinearIndependent.repr and LinearMap.exists_extend.
Proof: form the prescribed functional on the independent span using its genuine
coordinate inverse, then extend that linear form to the whole vector space. -/
theorem independent_prescribed_form {ι : Type*} (d : ι → V) (hd : LinearIndependent ℝ d) (w : ι → ℝ) :
    ∃ f : V →ₗ[ℝ] ℝ, ∀ i, f (d i)=w i := by
  -- Extension is used only for a separating proof, never as information available to a method.
  let f := (Finsupp.linearCombination ℝ w).comp hd.repr
  obtain ⟨F,hF⟩ := f.exists_extend
  refine ⟨F,fun i => ?_⟩
  let x : Submodule.span ℝ (Set.range d) := ⟨d i,Submodule.subset_span ⟨i,rfl⟩⟩
  have he := LinearMap.congr_fun hF x
  change F (d i)=Finsupp.linearCombination ℝ w (hd.repr x) at he
  rw [hd.repr_eq_single i x rfl,Finsupp.linearCombination_single,one_smul] at he
  exact he

/-- Scalar weights of the exact annihilator for a retained bidiagonal step family.
Use: the nonzero initial weight propagates through every nonzero missed and trial component.
Article: main_krylov, apA:prop:short, back substitution. -/
def shortWindowWeights (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => -(a k/b k)*shortWindowWeights a b k

omit [AddCommGroup V] [Module ℝ V] in
/-- Every back-substitution weight stays nonzero when all actual missed components and trials are nonzero.
Use: the retained-span annihilator detects the newest true CG direction.
Article: main_krylov, apA:prop:short, nonzero quotient coefficient.
Proof: finite induction multiplies the previous nonzero weight by a nonzero scalar quotient. -/
theorem shortWindowWeights_ne_zero (a b : ℕ → ℝ) (m : ℕ)
    (ha : ∀ i<m, a i≠0) (hb : ∀ i<m, b i≠0) : shortWindowWeights a b m≠0 := by
  induction m with
  | zero => exact one_ne_zero
  | succ m ih =>
    exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ha m (by omega)) (hb m (by omega))))
      (ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))

/-- The newest true independent direction is outside every retained nonzero bidiagonal step span.
Use: this is the full arbitrary-length obstruction underlying short-step XRFC, including the empty window.
Article: main_krylov, apA:prop:short, d_m⁰ modulo span{s₁,…,s_m} is nonzero.
Proof: prescribe the nonzero back-substitution weights on the independent
directions; their extended linear form kills every retained step and detects the newest direction. -/
theorem bidiagonal_last_not_mem (m : ℕ) (d : Fin (m+1) → V) (hd : LinearIndependent ℝ d)
    (a b : ℕ → ℝ) (ha : ∀ i<m, a i≠0) (hb : ∀ i<m, b i≠0) :
    d (Fin.last m)∉Submodule.span ℝ (Set.range (fun i : Fin m => a i.val • d i.castSucc+b i.val • d i.succ)) := by
  -- The annihilator gives the same exact obstruction as the article's printed quotient, with no determinant estimate.
  obtain ⟨f,hf⟩ := independent_prescribed_form d hd (fun i => shortWindowWeights a b i.val)
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin m => a i.val • d i.castSucc+b i.val • d i.succ))≤f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change f (a i.val • d i.castSucc+b i.val • d i.succ)=0
    rw [map_add,map_smul,map_smul,hf,hf]
    change a i.val*shortWindowWeights a b i.val+b i.val*shortWindowWeights a b (i.val+1)=0
    rw [shortWindowWeights]
    field_simp [hb i.val i.isLt]
    ring
  intro hv
  have hz := hspan hv
  change f (d (Fin.last m))=0 at hz
  rw [hf] at hz
  exact shortWindowWeights_ne_zero a b m ha hb hz

/-- Every nonzero missed newest component is outside the retained bidiagonal step span.
Use: the next virtual correction cannot equal the missed true CG displacement.
Article: main_krylov, apA:prop:short, (α_m−τ_m)d_m⁰ is not retained.
Proof: dividing membership by its nonzero scalar would put the newest direction in the already excluded span. -/
theorem bidiagonal_missed_not_mem (m : ℕ) (d : Fin (m+1) → V) (hd : LinearIndependent ℝ d)
    (a b : ℕ → ℝ) (ha : ∀ i<m, a i≠0) (hb : ∀ i<m, b i≠0) (c : ℝ) (hc : c≠0) :
    c • d (Fin.last m)∉Submodule.span ℝ (Set.range (fun i : Fin m => a i.val • d i.castSucc+b i.val • d i.succ)) := by
  intro hv
  apply bidiagonal_last_not_mem m d hd a b ha hb
  have h := Submodule.smul_mem (Submodule.span ℝ (Set.range
    (fun i : Fin m => a i.val • d i.castSucc+b i.val • d i.succ))) c⁻¹ hv
  rwa [smul_smul,inv_mul_cancel₀ hc,one_smul] at h

end
end krylov.Methods
