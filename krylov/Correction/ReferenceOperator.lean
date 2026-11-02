import krylov.Correction.PlanarAttainment
import krylov.Envelope.FreshDefect

/-!
Article: main_krylov, s4:eq:fL and thm:C, the actual reference staircase.
Use: apply the sharp spectral and Frobenius constants to the genuine CG flags
and the previously constructed fresh defect, retaining all finite horizons.
Source: the existing true reference flags, fresh-defect coordinates and sharp
aggregated compression inequalities. No separate chosen frame is introduced.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The source staircase operator on the actual canonical CG old flags.
Use: this is the geometric second-order factor paired with the existing fresh defect.
Article: main_krylov, s4:eq:fL, 𝓛=ΣP_l Ê_l P_l+Ê′. -/
def staircaseOperator (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (∑ l∈range (N-1), (oldFlag base g l).starProjection * cgOperator (E l) *
    (oldFlag base g l).starProjection)+cgOperator F

/-- The actual staircase action is the sum of its genuine projected increment actions.
Use: connect geometric formulas to the proved aggregated compression bounds.
Article: main_krylov, s4:eq:fL, action of 𝓛.
Proof: evaluate the true finite operator sum and its actual compositions. -/
theorem staircaseOperator_apply (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    staircaseOperator base g E F N v=
      (∑ l∈range (N-1), (oldFlag base g l).starProjection
        (cgOperator (E l) ((oldFlag base g l).starProjection v)))+cgOperator F v := by
  simp only [staircaseOperator,_root_.add_apply,_root_.sum_apply,mul_apply_eq_comp]

/-- The genuine last canonical CG unit step has norm one on its actual active horizon.
Use: discharge the unit-vector premise from true reference nonstagnation.
Article: main_krylov, thm:C, the terminal unit step ŝ_(N−1).
Proof: the already proved actual finite CG frame is orthonormal. -/
theorem terminal_unit_norm (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g) (hpos : 0<N) :
    ‖canonicalCGUnitStep base g (N-1)‖=1 :=
  (canonicalCGUnitStep_orthonormal base hb g N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hN))).norm_eq_one ⟨N-1,by omega⟩

/-- The true full-cycle last-step norm is exactly the actual penultimate canonical error norm.
Use: replace the computed reference step scale by the source error scale in the terminal expansion.
Article: main_krylov, thm:C, √c_last=‖e_(n−1)‖_A.
Proof: the genuine full CG frame forces actual termination, so the preceding
canonical gradient is the negative last step; its normalized direction has norm one. -/
theorem terminal_step_error_norm {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    ‖cgCanonicalError base g k‖=‖canonicalCGStep base g k‖ := by
  have ho := canonicalCGUnitStep_orthonormal base hb g (k+1)
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hN))
  have hh := canonicalCG_last_gradient base hb g ho
  change cgCanonicalError base g k= -‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k at hh
  rw [hh,norm_smul,Real.norm_of_nonpos (neg_nonpos.mpr (norm_nonneg _)),neg_neg]
  have hu : ‖canonicalCGUnitStep base g k‖=1 := by
    simpa only [Nat.add_sub_cancel] using terminal_unit_norm base hb g hN (by omega : 0<k+1)
  rw [hu,mul_one]

/-- The sharp spectral second-order bound holds on the actual CG flags and actual fresh defect.
Use: no abstract projection or terminal-vector premise remains in the source inequality.
Article: main_krylov, thm:C, ‖𝓛f̂‖≤K(W₀,ω′).
Proof: actual CG orthonormality supplies the last unit step, and genuine old-flag
orthogonality puts it in every relevant complementary subspace. Apply the
proved sharp compression theorem to precisely these true flags and increments. -/
theorem reference_second_order_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g) (hpos : 0<N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l∈range (N-1), (E l).IsSymm)
    (F : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ)
    (hω : ∀ l∈range (N-1), ‖E l‖≤ω l) {w : ℝ} (hF : ‖F‖≤w) :
    ‖staircaseOperator base g E F N (freshDefect base g E N)‖≤
      sharpConstant (∑ l∈range (N-1), ω l) w := by
  -- The reference geometry is derived from the genuine finite CG prefix.
  have hh (l : ℕ) (hl : l∈range (N-1)) :
      canonicalCGUnitStep base g (N-1)∈(oldFlag base g l)ᗮ :=
    unitStep_prefix_oldFlag_orthogonal base hb g hN (by omega) (mem_range.mp hl)
  have he := spectral_compression_bound (range (N-1)) (oldFlag base g)
    (fun l => cgOperator (E l)) (fun l hl =>
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hE l hl))))
    ω (fun l hl => by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hω l hl)
    _ hh (terminal_unit_norm base hb g hN hpos) (cgOperator F)
    (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hF)
  simpa only [staircaseOperator_apply,freshDefect,cgOperator] using he

/-- Frobenius budgets give the sharp square-root-two improvement on the genuine CG geometry.
Use: the norm-sensitive variant uses the same actual fresh defect and staircase.
Article: main_krylov, thm:C2(a), √2‖𝓛f̂‖≤K(W₀,ω′).
Proof: actual reference nonstagnation discharges the terminal unit and
orthogonality premises of the proved Frobenius compression theorem. -/
theorem reference_frobenius_second_order_bound
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g) (hpos : 0<N)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l∈range (N-1), (E l).IsSymm)
    (F : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ)
    (hω : ∀ l∈range (N-1), chebyshev1.hsNorm (E l)≤ω l)
    {w : ℝ} (hF : chebyshev1.hsNorm F≤w) :
    Real.sqrt 2*‖staircaseOperator base g E F N (freshDefect base g E N)‖≤
      sharpConstant (∑ l∈range (N-1), ω l) w := by
  have hh (l : ℕ) (hl : l∈range (N-1)) :
      canonicalCGUnitStep base g (N-1)∈(oldFlag base g l)ᗮ :=
    unitStep_prefix_oldFlag_orthogonal base hb g hN (by omega) (mem_range.mp hl)
  have he := frobenius_compression_bound (range (N-1)) (oldFlag base g) E hE ω hω
    _ hh (terminal_unit_norm base hb g hN hpos) (cgOperator F)
    (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using
      (spectral_le_hsNorm F).trans hF)
  simpa only [staircaseOperator_apply,freshDefect,cgOperator] using he

end
end krylov.Correction
