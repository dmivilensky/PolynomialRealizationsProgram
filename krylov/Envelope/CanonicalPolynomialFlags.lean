import krylov.Envelope.CanonicalInjections
import krylov.Envelope.NormTrace
import krylov.Envelope.PolynomialFlags

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine canonical polynomial flag geometry.
Use: propagate actual canonical CG flags under true polynomial actions
and prove the genuine error-polynomial orthogonality needed for absorption
of the real common tilt and unexplored first variation.
Source: standard commuting polynomial functional calculus, true reference
metric-root square and proved actual physical Krylov polynomial propagation.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Secant krylov.Stability Polynomial Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine positive reference metric root commutes with every actual polynomial of the true physical reference operator.
Use: The genuine positive reference metric root commutes with every actual polynomial of the true physical reference operator.
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine canonical polynomial flag geometry.
Proof: The actual reference operator is the true metric-root square, so the genuine root commutes with it and with every real polynomial action. -/
theorem root_polynomial_action (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (p : ℝ[X]) (v : EuclideanSpace ℝ (Fin n)) :
    cgOperator (metricRoot base) ((aeval (cgOperator base).toLinearMap p) v)=
      (aeval (cgOperator base).toLinearMap p) (cgOperator (metricRoot base) v) := by
  -- The true reference is the actual positive-root square, giving genuine operator and polynomial commutation.
  let R := cgOperator (metricRoot base)
  let Q := cgOperator base
  have hQ : Q.toLinearMap=R.toLinearMap*R.toLinearMap := by
    apply LinearMap.ext
    intro w
    change Matrix.toEuclideanCLM (𝕜 := ℝ) base w=Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) w)
    rw [← mul_apply_eq_comp,← map_mul,metricRoot_square base hb]
  have hc : Commute R.toLinearMap Q.toLinearMap := by
    rw [hQ]
    exact (mul_assoc _ _ _).symm
  exact polynomial_action_commute R.toLinearMap Q.toLinearMap hc p v

/-- Actual polynomial actions propagate genuine explored canonical CG vectors into the true degree-enlarged reference flag.
Use: Actual polynomial actions propagate genuine explored canonical CG vectors into the true degree-enlarged reference flag.
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine canonical polynomial flag geometry.
Proof: Use the true positive-root Krylov image, commute the actual root through the genuine polynomial, apply real physical Krylov propagation and transfer the actual finite flag inclusion. -/
theorem canonical_polynomial_mem_flag (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N r : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (p : ℝ[X]) {v : EuclideanSpace ℝ (Fin n)} (hv : v∈exploredFlag base g r)
    (hdegree : r+p.natDegree≤N) : (aeval (cgOperator base).toLinearMap p) v∈exploredFlag base g N := by
  -- Identify the real physical Krylov source flag and transfer its true polynomial growth through the actual metric root.
  have hpre (k : ℕ) (hk : k<N) : CG.gradient (cgOperator base) g k≠0 :=
    cg_nonstagnation base hb g k (hk.trans_le hcount)
  rw [exploredFlag_eq_primal_krylov base hb g r (fun i hi => hpre i (by omega))] at hv
  obtain ⟨w,hw,hv⟩ := hv
  change cgOperator (metricRoot base) w=v at hv
  rw [← hv,← root_polynomial_action base hb p w]
  rw [exploredFlag_eq_primal_krylov base hb g N hpre]
  apply Submodule.mem_map_of_mem
  exact krylovSpace_mono (cgOperator base) g hdegree (krylovSpace_polynomial (cgOperator base) g r p hw)

/-- A true polynomial of the actual reference operator applied to the genuine CG error is orthogonal to every actual old flag allowed by the real degree bound.
Use: A true polynomial of the actual reference operator applied to the genuine CG error is orthogonal to every actual old flag allowed by the real degree bound.
Article: main_krylov, apB:eq:F1 and apB:lem:mu(b), genuine canonical polynomial flag geometry.
Proof: Actual polynomial symmetry transfers the genuine action to the true old-flag test vector. Its real degree-enlarged flag is orthogonal to the actual reference CG error. -/
theorem canonical_polynomial_error_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N r : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (p : ℝ[X]) (hdegree : r+p.natDegree≤N) :
    (aeval (cgOperator base).toLinearMap p) (cgCanonicalError base g N)∈(exploredFlag base g r)ᗮ := by
  -- True polynomial symmetry moves the real action to an actual flag vector, whose genuine enlarged flag is orthogonal to the reference error.
  intro v hv
  have hs := polynomial_action_symmetric (cgOperator base).toLinearMap (cgOperator_positive base hb).1 p
  have he := hs (cgCanonicalError base g N) v
  change inner ℝ ((aeval (cgOperator base).toLinearMap p) (cgCanonicalError base g N)) v=
    inner ℝ (cgCanonicalError base g N) ((aeval (cgOperator base).toLinearMap p) v) at he
  rw [real_inner_comm,he,real_inner_comm]
  exact exploredFlag_error_orthogonal base hb g hcount _
    (canonical_polynomial_mem_flag base hb g N r hcount p hv hdegree)
end
end krylov.Envelope
