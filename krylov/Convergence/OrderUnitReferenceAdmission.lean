import krylov.Functions.NativeNormalizedReferences
import krylov.Correction.ResponseHomogeneity

/-!
Article: main_krylov, thm:D and s7:N, exact canonical error normalization.
Use: transfer the genuinely derived Euclidean-unit frozen-reference tube
to the metric-unit directions used in the printed sharp cycle constants.
A compact positive annulus preserves full atom counts; the zero-gradient
scale is excluded by the true unit metric condition, not an added margin.
Source: exact scalar homogeneity of genuine CG support and compact images.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Reference krylov.Functions krylov.Correction krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Genuine full frozen-reference admission on Euclidean unit directions
implies a derived compact full frozen family on canonical unit directions.
The admissibility predicate depends only on the actual physical start.
Article: main_krylov, thm:D, original s7:N normalization. -/
theorem canonical_unit_reference_admission
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (admission : E → Prop) (ep : ℝ) (hep : 0<ep)
    (F : Set E) (hF : IsCompact F) (hfull : ∀ g∈F,referenceAtomCount base hb g=n)
    (hcover : ∀ ε : ℝ,0<ε → ε<ep →∀ v : E,‖v‖=1 →admission (ε • v) →cgOperator base v∈F) :
    ∃ d : ℝ,0<d ∧∃ K : Set E,IsCompact K ∧
      (∀ g∈K,referenceAtomCount base hb g=n) ∧
      ∀ ε : ℝ,0<ε → ε<d →∀ u : E,‖cgOperator (metricRoot base) u‖=1 →admission (ε • u) →
        cgOperator base u∈K := by
  let S:=cgOperator (metricRoot base)
  let R:=cgOperator (metricRoot base)⁻¹
  let a:=(‖S‖+1)⁻¹
  let B:=‖R‖+1
  have ha : 0<a := by dsimp only [a];positivity
  have hB : 0<B := by dsimp only [B];positivity
  let K:=(fun z : ℝ × E=>z.1 • z.2) '' (Icc a B ×ˢ F)
  have hK : IsCompact K := (isCompact_Icc.prod hF).image (continuous_fst.smul continuous_snd)
  refine ⟨ep/(B+1),by positivity,K,hK,?_,?_⟩
  · rintro g ⟨⟨b,v⟩,⟨hbnd,hv⟩,rfl⟩
    rw [referenceAtomCount_scalar base hb v b ((ha.trans_le hbnd.1).ne')]
    exact hfull v hv
  · intro ε hε he u hunit hadmit
    have hSunit : ‖S u‖=1 := hunit
    have hu0 : u≠0 := by intro hz;rw [hz,map_zero,norm_zero] at hSunit;norm_num at hSunit
    have hun : 0<‖u‖ := norm_pos_iff.mpr hu0
    have hcancel : R (S u)=u := by
      simp only [R,S,cgOperator]
      rw [←mul_apply_eq_comp,←map_mul,Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
    have hupper : ‖u‖≤B := by
      have hh:=R.le_opNorm (S u)
      rw [hcancel,hSunit,mul_one] at hh
      exact hh.trans (by dsimp only [B];linarith)
    have hlower : a≤‖u‖ := by
      have hh:=S.le_opNorm u
      rw [hSunit] at hh
      dsimp only [a]
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (by positivity : 0<‖S‖+1)).mpr
      nlinarith only [hh,hun]
    let v:=‖u‖⁻¹ • u
    have hvunit : ‖v‖=1 := by
      dsimp only [v]
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hun.le),inv_mul_cancel₀ hun.ne']
    have hdecomp : (ε*‖u‖) • v=ε • u := by
      dsimp only [v]
      rw [smul_smul,mul_assoc,mul_inv_cancel₀ hun.ne',mul_one]
    have he' : ε*‖u‖<ep := by
      have hh:=(lt_div_iff₀ (by positivity : 0<B+1)).mp he
      nlinarith only [hh,mul_le_mul_of_nonneg_left hupper hε.le,hε]
    have hvF:=hcover (ε*‖u‖) (mul_pos hε hun) he' v hvunit (by rwa [hdecomp])
    refine ⟨(‖u‖,cgOperator base v),⟨⟨hlower,hupper⟩,hvF⟩,?_⟩
    dsimp only [v]
    rw [map_smul,smul_smul,mul_inv_cancel₀ hun.ne',one_smul]

end
end krylov.Convergence
