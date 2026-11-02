import krylov.Tensor.ReferenceProfile

/-!
Article: main_krylov, thm:Hp, the genuine reference amplification theorem.
Use: specialize tensor duality to the actual computed canonical CG frame,
actual midpoint differences and actual remaining energy-error tails.
Source: the proved finite flag duality and exact CG energy identities.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal TensorProduct
variable {n : ℕ}

/-- The true finite reference old flags, indexed by the actual active spectrum.
Article: main_krylov, thm:Hp. -/
def referenceFlagIndices (N : ℕ) (l : Fin (N-1)) : Finset (Fin N) :=
  univ.filter (fun i => i.val ≤ l.val)

/-- The actual compatible tensor response of a genuinely computed reference.
Article: main_krylov, thm:Hp, the original definition of Gamma_T. -/
def referenceCubicResponse (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n))
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  flagResponse (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
    (referenceFlagIndices _) (fun l => referenceMidpointDrift A g l.val)
    (fun l => remainingTail A g l.val) f

/-- The actual rank-one target paired with a direction of the genuine reference response.
Article: main_krylov, thm:Hp, the displayed Sym sum_i u_i e_i tensor sym N_i. -/
def referenceCubicTarget (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g u : EuclideanSpace ℝ (Fin n)) : ⨂[ℝ] _ : Fin 3, EuclideanSpace ℝ (Fin n) :=
  flagResponseTensor (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
    (referenceFlagIndices _) (fun l => referenceMidpointDrift A g l.val)
    (fun l => remainingTail A g l.val) u

/-- The actual reference tensor coefficient is attained and has the printed nuclear and energy-profile upper bounds.
Article: main_krylov, thm:Hp, exact duality and both upper inequalities.
Proof: use the genuine computed orthonormal CG frame in the attained flag
duality; the actual midpoint/tail budget has the proved two-error bound. -/
theorem reference_cubic_amplification [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hN : 2 ≤ referenceAtomCount A hA g) :
    ∃ Γ : ℝ≥0,
      IsGreatest ((fun u : EuclideanSpace ℝ (Fin n) =>
        2 * ‖tensorSymmetrization (referenceCubicTarget A hA g u)‖₊) '' {u | ‖u‖ = 1}) Γ ∧
      IsGreatest ((fun f : ContinuousMultilinearMap ℝ
          (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ => ‖referenceCubicResponse A hA g f‖) ''
        {f | IsSymmetricForm f ∧ ∀ x, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 2}) (Γ : ℝ) ∧
      (Γ : ℝ) ≤ referenceOperatorCoefficient A g (referenceAtomCount A hA g) ∧
      referenceOperatorCoefficient A g (referenceAtomCount A hA g) ≤
        ‖cgCanonicalError A g 0‖ * ‖cgCanonicalError A g 1‖ +
          (referenceAtomCount A hA g - 2 : ℕ) * ‖cgCanonicalError A g 1‖ ^ 2 := by
  obtain ⟨Γ, hΓ, hresp, hupper⟩ := flagResponse_nuclear_amplification
    (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
    (canonicalCG_frame A hA g) (referenceFlagIndices _)
    (fun l => referenceMidpointDrift A g l.val) (fun l => remainingTail A g l.val)
  refine ⟨Γ, hΓ, hresp, ?_, reference_operator_coefficient_le A hA g _ hN le_rfl⟩
  unfold referenceOperatorCoefficient
  rw [← Fin.sum_univ_eq_sum_range]
  exact hupper

end
end krylov.Tensor
