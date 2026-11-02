import krylov.Stability.AnalyticCorrection
import krylov.Methods.WindowCoordinates
import krylov.LinearAlgebra.EuclideanAsymptotics

/-!
Article: main_krylov, lem:projected-residual, real recorded-window residual orders.
Use: transfer an actual augmented-window residual order to its new real
normalized recorded step while retaining the actual old window.
Source: genuine inverse-Gram coordinates in the actual observed span,
finite coefficient regularity and the proved Euclidean coordinate asymptotic criterion.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.LinearAlgebra
open scoped Topology InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p : ℕ}

/-- A genuine nondegenerate recorded step in the actual augmented span preserves every normalized projected-residual order.
Use: repeated RFC residual orders pass to the actual old-plus-new recorded window, with no assumed coefficient expansion.
Article: main_krylov, lem:projected-residual, S_(k+1)ᵀg_(k+1)=O(ω^(c+1)).
Proof: actual nonzero columns make unnormalization locally bounded; genuine
inverse-Gram coefficients of the real recorded step are analytic and locally
bounded. Its true span identity transfers the residual order to its new unit
pairing, and each unchanged old unit coordinate inherits the same order. -/
theorem regular_recorded_projection_order (s : X → Fin (p+1) → E) (v g : X → E) (q : ℕ)
    (hs : ∀ i, AnalyticAt ℝ (fun z => s z i) 0) (hv : AnalyticAt ℝ v 0)
    (hn : ∀ i, s 0 i≠0) (hv0 : v 0≠0) (hG : (crossGram (s 0) (s 0)).det≠0)
    (hspan : ∀ᶠ z in 𝓝 (0 : X), v z∈Submodule.span ℝ (Set.range (s z)))
    (hρ : (fun z => projectedResidual (unitWindow (s z)) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q)) :
    (fun z => projectedResidual (unitWindow (Fin.cons (v z) (fun i : Fin p => s z i.succ))) (g z)) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^q) := by
  -- Coordinates of the actual recorded vector are computed from its genuine raw Gram matrix, then bounded locally.
  have hsn : ∀ᶠ z in 𝓝 (0 : X), ∀ i, s z i≠0 :=
    Filter.eventually_all.mpr fun i => (hs i).continuousAt.eventually_ne (hn i)
  have hraw (i : Fin (p+1)) : (fun z => inner ℝ (s z i) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q) := by
    have hi := (euclidean_bigO_iff_entry _ _).mp hρ i
    have ht := ((hs i).continuousAt.norm.tendsto.isBigO_one ℝ).mul hi
    apply (ht.congr_right (fun z => one_mul (‖z‖^q))).congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hsn] with z hzs
    change ‖s z i‖*inner ℝ (‖s z i‖⁻¹ • s z i) (g z)=inner ℝ (s z i) (g z)
    rw [real_inner_smul_left,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hzs i)),one_mul]
  let c := fun z => conjugacyCoefficients (s z) (s z) (v z)
  have hc (i : Fin (p+1)) : AnalyticAt ℝ (fun z => c z i) 0 :=
    analytic_conjugacyCoefficients s s v 0 hs hs hv hG i
  have hdet := analytic_matrix_det (fun z => crossGram (s z) (s z)) 0 (fun i j => analytic_inner (hs i) (hs j))
  have hunit : ∀ᶠ z in 𝓝 (0 : X), IsUnit (crossGram (s z) (s z)).det :=
    (hdet.continuousAt.eventually_ne hG).mono fun _ hz => isUnit_iff_ne_zero.mpr hz
  have hterms : ∀ i∈(Finset.univ : Finset (Fin (p+1))),
      (fun z => c z i*inner ℝ (s z i) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q) := by
    intro i _
    simpa only [one_mul] using ((hc i).continuousAt.tendsto.isBigO_one ℝ).mul (hraw i)
  have hsum : (fun z => ∑ i, c z i*inner ℝ (s z i) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q) :=
    (Asymptotics.IsBigO.sum hterms).congr_left fun z => by simp only [Finset.sum_apply]
  have hinner : (fun z => inner ℝ (v z) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q) := by
    apply hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [hunit,hspan] with z hz hvs
    simpa only [combine,sum_inner,real_inner_smul_left] using
      congrArg (fun w => inner ℝ w (g z)) (combine_gram_coordinates (s z) (v z) hz hvs)
  have hinv : (fun z => ‖v z‖⁻¹) =O[𝓝 (0 : X)] (fun _ => (1 : ℝ)) :=
    (hv.continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr hv0)).tendsto.isBigO_one ℝ
  have hnew : (fun z => inner ℝ (‖v z‖⁻¹ • v z) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q) := by
    simpa only [one_mul,real_inner_smul_left] using hinv.mul hinner
  apply (euclidean_bigO_iff_entry _ _).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [projectedResidual,coordinates,unitWindow,rescaleWindow,Fin.cons_zero] using hnew
  · simpa only [projectedResidual,coordinates,unitWindow,rescaleWindow,Fin.cons_succ] using
      (euclidean_bigO_iff_entry _ _).mp hρ j.succ

end
end krylov.Stability
