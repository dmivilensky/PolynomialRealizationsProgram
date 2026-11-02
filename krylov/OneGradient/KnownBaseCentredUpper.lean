import krylov.OneGradient.KnownBaseCentreCoordinates
import krylov.OneGradient.HiddenPlaneInverseUpper
import krylov.OneGradient.TwoQueryPhysicalGame
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), genuine physical centring upper bound.
Use: the actual history-only M1 algorithm has the sharp V2 leading
coefficient uniformly over the original relative-budget physical scenarios.
Source: genuine observed-column dictionary, complete known CG geometry,
the actual hidden-plane inverse bound and exact positive-root transport.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual centring algorithm's semantic output satisfies the finite
original physical error estimate, uniformly over every symmetric second
segment and every budgeted unevaluated output segment. The normalization
is the true penultimate reference energy error. No regularity of the
unknown scenario, centre rule or final output policy is required.
Use: the genuine M1 implementation attains V2 with an explicit common
cubic remainder before any limiting supremum is taken.
Article: main_krylov, thm:local(c), true known-base minimax upper candidate.
Proof: normalize the actual physical increment by its positive allowance.
Its true relative budget yields a symmetric contraction. The real native
queries give exactly its observed column, and the actual output is the
inverse of that column's centre. Exact physical/canonical transport then
reduces the genuine output gradient to the full-disc finite inverse bound. -/
theorem knownBaseCentredMethod_physical_upper
    (base C B : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (hC : C.IsSymm)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2)
    (W w omega : ℝ) (hW : 0< W) (hw : 0≤ w) (homega : 0< omega)
    (hsmall : W*omega≤(1/2 : ℝ))
    (hbudget : relativeBudget base (C-base)≤ W*omega)
    (houtput : relativeBudget base (B-C)≤ w*omega) :
    let m := knownBaseCentredMethod base (W*omega)
    let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
    ‖cgOperator (metricRoot base)⁻¹ (m.outputGradient (cgOperator B) H)‖≤
      ‖cgCanonicalError base g 1‖*
        (twoDimensionalValue W w*omega^2+2*W^2*(W+w)*omega^3) := by
  let eta := W*omega
  let M := eta⁻¹ • relativeOperator base (C-base)
  let m := knownBaseCentredMethod base eta
  let H := oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator C)) g 2
  let e := canonicalCGUnitStep base g 0
  let h := canonicalCGUnitStep base g 1
  let sigma := ‖canonicalCGStep base g 1‖
  let rho := (eta*sigma) • cgOperator M h
  let F := cgOperator (relativeOperator base (B-C))
  have heta : 0< eta := mul_pos hW homega
  have hrel : relativeOperator base (C-base)=eta • M := by
    dsimp only [M]
    rw [smul_smul,mul_inv_cancel₀ heta.ne',one_smul]
  have hMs : M.IsSymm := (relativeOperator_isSymm base (C-base) (hC.sub hb.isHermitian.isSymm)).smul _
  have hMn : ‖M‖≤1 := by
    change ‖eta⁻¹ • relativeOperator base (C-base)‖≤1
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr heta.le)]
    have hn : ‖relativeOperator base (C-base)‖≤ eta := hbudget
    exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr heta.le)).trans_eq (inv_mul_cancel₀ heta.ne')
  have hFn : ‖F‖≤ w*omega := by
    rw [show ‖F‖=relativeBudget base (B-C) from (Matrix.l2_opNorm_toEuclideanCLM _).symm]
    exact houtput
  obtain ⟨he,hh,heh,hfull⟩ := knownBaseCentre_reference_plane base hb g hc
  have hscale := knownBaseCentre_reference_scale base hb g hc
  have hcolumn : cgOperator (metricRoot base)⁻¹ H.gradient=rho :=
    knownBaseCentre_observed_column base C M hb eta g hc hrel
  have hu := knownBaseCentre_output_coordinates base C M hb eta heta g hc hrel
  have hB : relativeOperator base B=1+eta • M+relativeOperator base (B-C) := by
    have hsplit : B=base+(C-base)+(B-C) := by abel
    calc
      relativeOperator base B=relativeOperator base base+
          relativeOperator base (C-base)+relativeOperator base (B-C) := by
        conv_lhs => arg 2;rw [hsplit]
        simp only [relativeOperator,Matrix.mul_add,Matrix.add_mul]
      _ = _ := by rw [relativeOperator_base base hb,hrel]
  have hcoords := twoQuery_canonical_output base B hb m H
  have hBop : cgOperator (relativeOperator base B)=cgOperator (1+eta • M)+F := by
    rw [hB]
    exact map_add (Matrix.toEuclideanCLM (𝕜 := ℝ)) _ _
  rw [hcolumn,hBop,_root_.add_apply] at hcoords
  have hupper := hiddenPlane_centred_inverse_upper M hMs hMn e h he hh heh hfull
    W w omega sigma hW hw homega.le (norm_nonneg _) hsmall F hFn
  dsimp only at hu hupper ⊢
  change ‖cgOperator (metricRoot base)⁻¹ (m.outputGradient (cgOperator B) H)‖≤_
  change cgOperator (metricRoot base) (m.output H)=_ at hu
  rw [hcoords,← add_assoc,hu,hscale.2]
  exact hupper

end
end krylov.OneGradient
