import krylov.Convergence.OrderTensorConstants
import krylov.Cancellation.DeferredFullProfile

/-!
Article: main_krylov, thm:D, exact printed data-midpoint DC restart constant.
Use: bound the genuine compatible third-derivative deferred response with
its actual damping, full CG energies and Chebyshev error profile. The
constant is precisely the source sum, before native function substitution.
Source: the proved deferred tail geometry, Banach's cubic norm identity,
and the genuine full-reference Chebyshev energy majorant.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Variation krylov.Stability krylov.Design krylov.Secant krylov.Cancellation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- The actual compatible deferred tensor response satisfies exactly the
printed Chebyshev DC cycle constant, at the true canonical unit scale.
Article: main_krylov, thm:D, DC. -/
theorem dc_spatial_tensor_restart_constant
    (I : chebyshev1.SpectralInterval)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (T : SymmetricCubic E)
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (hband : ∀ i,I.mu≤hb.1.eigenvalues i ∧hb.1.eigenvalues i≤I.mu*I.kappa)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=k+1)
    (hu : ‖cgOperator (metricRoot base) u‖=1)
    (epsilon ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1) (hepsilon : |epsilon|≤ρ) :
    ‖deferredResponse base (cgOperator base u) k epsilon (fcCompatibleIncrements base hb D u)‖≤
      m*dcRestartConstant (designSpacing I) ρ k := by
  let g:=cgOperator base u
  have hcg : referenceAtomCount base hb g=k+1 := hc
  let R:=orderUnitReference I base hb u hc hband
  let q:=fun l : ℕ=>jacobi.Young.sech ((l:ℝ)*designSpacing I)
  have hunit : R.initialNorm=1 := (orderUnitReference_initialNorm I base hb u hc hband).trans hu
  have hprof l : ‖cgCanonicalError base g l‖≤q l := by
    have hh:=reference_error_chebyshev I R l
    rw [hunit,mul_one,epsilon_eq_sech] at hh
    exact hh
  have hbudget l (hl : l<k) : ‖fcCompatibleIncrements base hb D u l‖≤m*‖cgCanonicalError base g l‖ := by
    rw [fcCompatibleIncrements_eq_own,ownFCCompatibleIncrements_third_tensor base hb D T hT,cubicSliceMatrix_norm]
    have hs:=cubic_slice_norm_le T (2*m) (by positivity) hdiag (referenceMidpointDrift base g l)
    have hd:=reference_midpoint_drift_le base hb g l (by omega)
    exact hs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hm])
  have hρsq : 0≤1-ρ^2 := by nlinarith only [hρ,hρ1]
  have htail l (hl : l<k) : ‖deferredTail base g k epsilon l‖≤
      Real.sqrt (ρ^2*(q (l+1))^2+(1-ρ^2)*(q k)^2) := by
    have hmono:=deferred_tail_norm_mono base hb g k l hl (by omega) epsilon ρ (by rwa [abs_of_nonneg hρ])
    have hn:=deferred_tail_norm_sq base hb g k l hl (by omega) ρ
    have henergy : cgEnergy base g k=‖cgCanonicalError base g k‖^2 := by
      have he:=congrArg (fun a : ℝ=>a^2) (last_energy_error_norm base hb g k (by omega))
      rw [Real.sq_sqrt (by rw [cgEnergy_eq_norm_sq base hb];exact sq_nonneg _)] at he
      exact he
    rw [henergy] at hn
    have hfirst:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hprof (l+1)) 2) (sq_nonneg ρ)
    have hlast:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hprof k) 2) hρsq
    have hbnd : ‖deferredTail base g k ρ l‖^2≤ρ^2*(q (l+1))^2+(1-ρ^2)*(q k)^2 := by
      nlinarith only [hn,hfirst,hlast]
    exact hmono.trans ((Real.sqrt_sq (norm_nonneg _)).symm.le.trans (Real.sqrt_le_sqrt hbnd))
  apply (deferred_response_le base g k epsilon (fcCompatibleIncrements base hb D u)
    (fun l=>m*‖cgCanonicalError base g l‖) hbudget).trans
  rw [dcRestartConstant,mul_sum]
  apply sum_le_sum
  intro l hl
  have hprod:=mul_le_mul (mul_le_mul_of_nonneg_left (hprof l) hm) (htail l (mem_range.mp hl))
    (norm_nonneg _) (mul_nonneg hm (jacobi.Young.sech_pos _).le)
  exact hprod.trans_eq (by dsimp only [q];push_cast;ring)

end
end krylov.Convergence
