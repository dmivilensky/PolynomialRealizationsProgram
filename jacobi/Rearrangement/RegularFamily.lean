import jacobi.Rearrangement.PolarizationContinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Nonnegative functions with a common bound, Lipschitz constant and compact
support form a compact set in the uniform norm. Restriction to a compact
interval and extension by clamping reduce this assertion to mathlib's
Arzela–Ascoli theorem. This supplies actual compactness for the regular
polarization orbit, before approximation of arbitrary finite-energy densities.
Source: Arzela–Ascoli and the polarization construction in Lieb and Loss, Analysis.
Use: a compact ambient set containing every centered polarization of a regular density.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Metric
open scoped NNReal Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- Uniformly bounded nonnegative Lipschitz functions vanishing outside a fixed interval.
Use: a compact ambient set containing every centered polarization of a regular density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def regularFamily (R C : ℝ) (K : ℝ≥0) : Set (ℝ →ᵇ ℝ) :=
  {f | LipschitzWith K f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ C) ∧ (∀ x, R ≤ |x| → f x=0)}

/-- The regular family is closed in the uniform norm.
Use: taking the compact closure of a polarization orbit preserves all regularity bounds.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: evaluation is continuous; nonnegativity, upper bounds, vanishing and
the common Lipschitz bound are closed conditions. -/
theorem regularFamily_closed (R C : ℝ) (K : ℝ≥0) : IsClosed (regularFamily R C K) := by
  -- All constraints are pointwise closed, including the two endpoints of the support interval.
  have hL : IsClosed {f : ℝ →ᵇ ℝ | LipschitzWith K f} :=
    (show IsClosed {f : ℝ → ℝ | LipschitzWith K f} from
      isClosed_setOfPred_lipschitzWith K).preimage BoundedContinuousFunction.continuous_coe
  have hb : IsClosed {f : ℝ →ᵇ ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ C} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => (isClosed_le continuous_const
      (BoundedContinuousFunction.lipschitz_eval_const x).continuous).inter
        (isClosed_le (BoundedContinuousFunction.lipschitz_eval_const x).continuous continuous_const)
  have hz : IsClosed {f : ℝ →ᵇ ℝ | ∀ x, R ≤ |x| → f x=0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq (BoundedContinuousFunction.lipschitz_eval_const x).continuous continuous_const
  exact hL.inter (hb.inter hz)

/-- The actual regular family on the whole line is compact in the uniform norm.
Use: guarantees attainment of a radial test functional on the closed polarization orbit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: Arzela–Ascoli gives compactness after restriction to [-R,R]. Clamping
extends restricted functions continuously and nonexpansively to the line.
Every member of the closed whole-line family is such an extension. -/
theorem regularFamily_compact {R : ℝ} (hR : 0 ≤ R) (C : ℝ) (K : ℝ≥0) :
    IsCompact (regularFamily R C K) := by
  -- Work on the compact interval, where one common Lipschitz modulus gives equicontinuity.
  let X := Icc (-R) R
  let A : Set (X →ᵇ ℝ) := {f | LipschitzWith K f ∧ ∀ x, 0 ≤ f x ∧ f x ≤ C}
  have hA : IsClosed A := by
    apply IsClosed.inter
    · exact (show IsClosed {f : X → ℝ | LipschitzWith K f} from
        isClosed_setOfPred_lipschitzWith K).preimage BoundedContinuousFunction.continuous_coe
    · change IsClosed {f : X →ᵇ ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ C}
      simp only [ofPred_forall]
      exact isClosed_iInter fun x => (isClosed_le continuous_const
        (BoundedContinuousFunction.lipschitz_eval_const x).continuous).inter
          (isClosed_le (BoundedContinuousFunction.lipschitz_eval_const x).continuous continuous_const)
  have he : Equicontinuous ((↑) : A → X → ℝ) := by
    apply equicontinuous_of_continuity_modulus (fun t => (K : ℝ)*t)
    · convert ((continuous_const.mul continuous_id :
        Continuous (fun t : ℝ => (K : ℝ)*t)).tendsto 0) using 1
      simp
    · intro x y f
      exact f.property.1.dist_le_mul x y
  have hc : IsCompact A := BoundedContinuousFunction.arzela_ascoli₂ (Icc 0 C)
    isCompact_Icc A hA (fun f x hf => hf.2 x) he
  -- Clamping supplies a continuous extension operator; no unproved extension theorem is used.
  let clamp : C(ℝ, X) := ⟨projIcc (-R) R (by linarith), continuous_projIcc⟩
  let ext : (X →ᵇ ℝ) → (ℝ →ᵇ ℝ) := fun f => f.compContinuous clamp
  have hi : IsCompact (ext '' A) := hc.image
    (BoundedContinuousFunction.continuous_compContinuous clamp)
  apply hi.of_isClosed_subset (regularFamily_closed R C K)
  intro f hf
  let g : X →ᵇ ℝ := f.compContinuous ⟨Subtype.val, continuous_subtype_val⟩
  have hg : g ∈ A := ⟨by
    simpa only [g,BoundedContinuousFunction.coe_compContinuous,ContinuousMap.coe_mk,mul_one]
      using hf.1.comp (LipschitzWith.subtype_val X),
    fun x => hf.2.1 x⟩
  refine ⟨g,hg,?_⟩
  dsimp only [ext,g,BoundedContinuousFunction.compContinuous]
  apply BoundedContinuousFunction.ext
  intro x
  change f (projIcc (-R) R (by linarith) x)=f x
  by_cases hx : x ∈ Icc (-R) R
  · rw [projIcc_of_mem _ hx]
  · have hout : x < -R ∨ R < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
    rcases hout with hx | hx
    · rw [projIcc_of_le_left _ hx.le]
      exact (hf.2.2 (-R) (by simpa only [abs_neg,abs_of_nonneg hR] using le_refl R)).trans
        (hf.2.2 x (by rw [abs_of_nonpos (by linarith)]; linarith)).symm
    · rw [projIcc_of_right_le _ hx.le]
      exact (hf.2.2 R (by simpa only [abs_of_nonneg hR] using le_refl R)).trans
        (hf.2.2 x (by rw [abs_of_nonneg (by linarith)]; linarith)).symm

/-- A centered left polarization preserves the common compact support and regular bounds.
Use: keeps every regular polarization orbit inside the compact ambient family.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: on the preferred half-line reflection moves a point farther from zero;
on the other half-line the minimum includes the original zero value. -/
theorem polarize_regular {m : ℝ →ᵇ ℝ} {R C a : ℝ} {K : ℝ≥0}
    (hm : m ∈ regularFamily R C K) (ha : 0 ≤ a) :
    LipschitzWith K (polarize a m) ∧
      (∀ x, 0 ≤ polarize a m x ∧ polarize a m x ≤ C) ∧
      (∀ x, R ≤ |x| → polarize a m x=0) := by
  -- Sorting keeps the range bound; only support on the preferred side needs a distance comparison.
  refine ⟨polarize_lipschitz hm.1 a,fun x => ?_,fun x hx => ?_⟩
  · rcases polarize_eq_or a m x with h | h <;> rw [h] <;> exact hm.2.1 _
  · unfold polarize
    split_ifs with h
    · have hd : |x| ≤ |reflect a x| := by
        dsimp [reflect]
        grind [abs_eq_max_neg]
      rw [hm.2.2 x hx,hm.2.2 _ (hx.trans hd),max_self]
    · rw [hm.2.2 x hx,min_eq_left (hm.2.1 _).1]

end
end jacobi.Rearrangement
