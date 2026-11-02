import krylov.Correction.FullReconstruction
import krylov.Stability.CanonicalResponseCoordinates
import krylov.Stability.WeightedCGFlags

/-!
Article: main_krylov, thm:UCq, uniform reference-weighted terminal flags.
Use: Compare the actual old recorded directions with CG while allowing the
actual last raw direction and true last reference energy to be arbitrarily small.
Source: the existing genuine CG weighted rank-one estimate, spectral-ratio
cancellation and real full-basis inverse-Gram flag bound.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- True old recorded-step errors and the genuine full Gram bound give a dimension-and-condition-ratio terminal reference-weighted flag allowance without comparing the last raw direction to its CG value.
Use: Supply the actual old-flag comparison in the uniform cubic RFC coefficient.
Article: main_krylov, thm:UCq.
Proof: Keep the actual penultimate CG error norm on each old normalized rank-one change. The existing true CG geometry cancels the positive spectral scale and bounds these weighted changes by the recorded-step error. The genuine inverse-Gram flag estimate then adds only the full measured Gram error; monotonicity bounds its reference weight by the initial unit error. No individual CG energy is inverted.
-/
theorem terminal_recorded_weighted_flags
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    {μ κ : ℝ} (hμ : 0<μ) (hκ : 1≤κ)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (t : Fin n → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    {a D ε : ℝ} (hD : 0≤D) (hε : 0≤ε)
    (hGram : ‖(fullBasisMatrix t)ᵀ*fullBasisMatrix t-1‖≤a*ε) (haε : a*ε≤1/2)
    (hx : ∀ i<n-1, x i≠0)
    (ht : ∀ i : Fin n, i.val<n-1 → t i=NormedSpace.normalize (x i.val))
    (hstep : ∀ i<n-1, ‖x i-canonicalCGStep base g i‖≤D*ε) :
    ∀ l<n-1, ‖cgCanonicalError base g (n-1)‖*
      ‖transportedFlag (fullBasisMatrix t) l-transportedFlag (canonicalCGUnitMatrix base g) l‖≤
      (3*a+4*(n : ℝ)*Real.sqrt κ*D)*ε := by
  intro l hl
  let T := fullBasisMatrix t
  let Q := canonicalCGUnitMatrix base g
  let w := ‖cgCanonicalError base g (n-1)‖
  have hw : w≤1 := (cgError_antitone base hb g (show 0≤n-1 by omega)).trans hinit
  have hβ : 0≤4*Real.sqrt κ*(D*ε) := by positivity
  have hcol : ∀ j∈univ.filter (fun j : Fin n => j.val≤l),
      w*‖vecMulVec (fun i => T i j) (fun i => T i j)-
        vecMulVec (fun i => Q i j) (fun i => Q i j)‖≤4*Real.sqrt κ*(D*ε) := by
    intro j hj
    have hjl := (mem_filter.mp hj).2
    have hjold : j.val<n-1 := by omega
    have hr := cg_weighted_rankOne base hb g hμ (by nlinarith : μ≤μ*κ) hspec
      (show j.val<referenceAtomCount base hb g by omega) (show j.val≤n-1 by omega)
      (x j.val) (hx j.val hjold) (D*ε) (hstep j.val hjold)
    change w*‖vecMulVec (WithLp.ofLp (t j)) (WithLp.ofLp (t j))-
      vecMulVec (WithLp.ofLp (canonicalCGUnitStep base g j.val))
        (WithLp.ofLp (canonicalCGUnitStep base g j.val))‖≤_
    rw [rankOne_matrix_difference_norm,ht j hjold]
    simpa only [mul_div_cancel_left₀ _ hμ.ne'] using hr
  have hbound := transportedFlag_weighted_bound T Q l (hGram.trans haε) (norm_nonneg _) hβ hcol
  have hflagQ : Q*prefixProjection n l*Qᵀ=transportedFlag Q l := by
    unfold transportedFlag
    rw [show Q⁻¹=Qᵀ from canonicalCGUnitMatrix_inverse base hb g hcount]
  rw [hflagQ] at hbound
  have hfirst : 3*w*‖Tᵀ*T-1‖≤3*(a*ε) := by
    calc
      _ ≤ 3*‖Tᵀ*T-1‖ := mul_le_mul_of_nonneg_right (by linarith : 3*w≤3) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hGram (by norm_num)
  exact hbound.trans ((add_le_add hfirst (le_refl _)).trans_eq (by ring))

end
end krylov.Correction
