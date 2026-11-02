import krylov.Functions.HarmonicRatio
import krylov.Functions.MetricCubicSelfConcordant

/-!
Article: main_krylov, thm:H, the actual harmonic native RFC realization.
Use: assemble the genuine scalar physical objective, exact printed
self-concordant radius and literal leading one-half native gradient norm.
Every source derivative and local execution estimate is derived from the
function formula and the original positive n-atom reference.
Source: the actual scalar harmonic construction and proved native transfer.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Reference krylov.Nonlinear krylov.Secant krylov.Tensor krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The actual harmonic function in the original physical minimizer metric
has the printed self-concordant radius and the exact one-half native RFC
leading gradient norm. Its dimensionless multiplier has proved error <=2r.
Article: main_krylov, thm:H, cubic realization. -/
theorem harmonic_nativeRFC_realization
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 2 ≤ k)
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hN : referenceAtomCount base hb (cgOperator base u)=k+1)
    {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1) :
    let T := referenceHarmonicTensor base hb (cgOperator base u) (1-δ)
    let f := metricCubicObjective (metricCoordinates base hb) T
    0<canonicalCubicRadius (1-δ) ∧
      IsStandardSelfConcordantOn f
        ((metricCoordinates base hb) ⁻¹' ball 0 (canonicalCubicRadius (1-δ))) ∧
      ∃ r : ℝ, 0<r ∧ ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧
        ∀ ε : ℝ, 0<ε → ε<ε₀ →
          |‖cgOperator (metricRoot base)⁻¹
              (gradient f (rfcFunctionPoint (metricCoordinates base hb) f
                (metricCubicGradient (metricCoordinates base hb) T) fullMemory r (ε • u) (k+1)))‖ -
            ε^3*((1/2 : ℝ)*(1-δ)^2*cgEnergy base (cgOperator base u) 0*
              ‖cgCanonicalError base (cgOperator base u) k‖*
              harmonicResponseRatio (‖canonicalCGStep base (cgOperator base u) k‖/
                ‖canonicalCGStep base (cgOperator base u) 0‖))| ≤ η*ε^3 := by
  dsimp only
  let g := cgOperator base u
  let T := referenceHarmonicTensor base hb g (1-δ)
  let S := metricCoordinates base hb
  have hcount : 3≤referenceAtomCount base hb g := by rw [hN]; omega
  let i0 : Fin (referenceAtomCount base hb g) := ⟨0,by omega⟩
  let il : Fin (referenceAtomCount base hb g) := ⟨referenceAtomCount base hb g-1,by omega⟩
  have hframe := canonicalCG_frame base hb g
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0 ≠ il by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega)
  have hd : ∀ v : EuclideanSpace ℝ (Fin (k+1)), ‖v‖=1 → |T.form v v v|≤2*(1-δ) :=
    canonicalHarmonicTensor_bound _ _ he hh heh (by linarith)
  obtain ⟨hradius,hsc⟩ := metricCubic_selfConcordant_radius S
    (metricCoordinates_forward_symmetric base hb) T (by linarith : 0<1-δ) (by linarith : 1-δ<1) hd
  refine ⟨hradius,hsc,?_⟩
  obtain ⟨r,hr,hbound⟩ := metricCubic_nativeRFC_spatial base hb (by omega) T u hN
  refine ⟨r,hr,?_⟩
  intro η hη
  obtain ⟨ep,hep,hp⟩ := hbound η hη
  refine ⟨ep,hep,?_⟩
  intro ε hε heε
  have hv := hp ε hε heε
  let v := cgOperator (metricRoot base)⁻¹ (gradient (metricCubicObjective S T)
    (rfcFunctionPoint S (metricCubicObjective S T) (metricCubicGradient S T) fullMemory r (ε • u) (k+1)))
  let c := rfcTensorCanonicalCoefficient base hb (metricCubicVariation S T) u
  have hn := (abs_norm_sub_norm_le v (-(ε^3 • c))).trans
    (show ‖v-(-(ε^3 • c))‖≤η*ε^3 by simpa only [sub_neg_eq_add] using hv)
  rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hε 3)] at hn
  have hc := rfc_harmonic_half_coefficient base hb u hk (1-δ) (by linarith) hN
  change ‖c‖ = _ at hc
  rw [hc] at hn
  exact hn

end
end krylov.Functions
