import polyak.Growth.GramRealization
import Mathlib.Topology.Sequences

/-!
Article: Appendix C, compactness of the actual finite-dimensional price coefficients.
Use: a uniform absolute coefficient bound gives a genuine convergent subsequence
of continuous linear functionals on the concrete Gram-and-value window space.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth.FiniteHorizon Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

abbrev WindowPrice (H : ℕ) := WindowSpace H →L[ℝ] ℝ

def priceCoefficients {H : ℕ} (L : WindowPrice H) : WindowSpace H :=
  (fun i j => L (matrixCoordinate i j),fun i => L (valueBasis i))

def windowMatrixCoordinate {H : ℕ} (i j : Fin (H+2)) : WindowPrice H :=
  (ContinuousLinearMap.proj j : (Fin (H+2) → ℝ) →L[ℝ] ℝ) ∘L
    (ContinuousLinearMap.proj i : WindowMatrix H →L[ℝ] (Fin (H+2) → ℝ)) ∘L
    ContinuousLinearMap.fst ℝ (WindowMatrix H) (Fin H → ℝ)

def priceOfCoefficients {H : ℕ} (c : WindowSpace H) : WindowPrice H :=
  (∑ i,∑ j,c.1 i j • windowMatrixCoordinate i j)+∑ i,c.2 i • valueCoordinate i

@[simp] theorem windowMatrixCoordinate_apply {H : ℕ} (i j : Fin (H+2)) (Y : WindowSpace H) :
    windowMatrixCoordinate i j Y=Y.1 i j := rfl

theorem priceOfCoefficients_apply {H : ℕ} (c Y : WindowSpace H) :
    priceOfCoefficients c Y=(∑ i,∑ j,c.1 i j*Y.1 i j)+∑ i,c.2 i*Y.2 i := by
  simp only [priceOfCoefficients,add_apply,sum_apply,smul_apply,smul_eq_mul,windowMatrixCoordinate_apply]
  rfl

theorem priceOfCoefficients_inverse {H : ℕ} (L : WindowPrice H) :
    priceOfCoefficients (priceCoefficients L)=L := by
  apply ContinuousLinearMap.ext
  intro Y
  rw [priceOfCoefficients_apply]
  conv_rhs => rw [window_coordinate_expansion Y]
  simp only [priceCoefficients,map_add,map_sum,map_smul,smul_eq_mul]
  simp_rw [mul_comm]

@[fun_prop] theorem continuous_priceOfCoefficients_apply {H : ℕ} (Y : WindowSpace H) :
    Continuous (fun c : WindowSpace H => priceOfCoefficients c Y) := by
  simp only [priceOfCoefficients_apply]
  fun_prop

theorem priceSize_nonneg {H : ℕ} (L : WindowPrice H) : 0≤priceSize L := by
  unfold priceSize
  positivity

/-- All actual price coordinates are bounded by the absolute coefficient sum. -/
theorem norm_priceCoefficients_le {H : ℕ} (L : WindowPrice H) :
    ‖priceCoefficients L‖≤priceSize L := by
  have hM : 0≤∑ i,∑ j,|L (matrixCoordinate i j)|:=by positivity
  have hV : 0≤∑ i,|L (valueBasis i)|:=by positivity
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (priceSize_nonneg L)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (priceSize_nonneg L)).mpr
    intro j
    have h0 : |L (matrixCoordinate i j)|≤∑ j,|L (matrixCoordinate i j)|:=
      Finset.single_le_sum (f:=fun j : Fin (H+2) => |L (matrixCoordinate i j)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h1 : (∑ j,|L (matrixCoordinate i j)|)≤∑ i,∑ j,|L (matrixCoordinate i j)|:=
      Finset.single_le_sum (f:=fun i : Fin (H+2) => ∑ j,|L (matrixCoordinate i j)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    change |L (matrixCoordinate i j)|≤priceSize L
    unfold priceSize
    linarith
  · apply (pi_norm_le_iff_of_nonneg (priceSize_nonneg L)).mpr
    intro i
    have hi : |L (valueBasis i)|≤∑ i,|L (valueBasis i)|:=
      Finset.single_le_sum (f:=fun i : Fin H => |L (valueBasis i)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    change |L (valueBasis i)|≤priceSize L
    unfold priceSize
    linarith

/-- Compactness is proved in the concrete coefficient space, not assumed for prices. -/
theorem exists_price_subsequence {H : ℕ} (L : ℕ → WindowPrice H) {M : ℝ}
    (hM : ∀ n, priceSize (L n)≤M) :
    ∃ Lstar : WindowPrice H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ Y : WindowSpace H, Tendsto (fun n => L (φ n) Y) atTop (𝓝 (Lstar Y)) := by
  have hb (n : ℕ) : priceCoefficients (L n)∈Metric.closedBall (0 : WindowSpace H) M := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_priceCoefficients_le (L n)).trans (hM n)
  obtain ⟨c,_,φ,hφ,hc⟩:=(isCompact_closedBall (0 : WindowSpace H) M).tendsto_subseq hb
  refine ⟨priceOfCoefficients c,φ,hφ,?_⟩
  intro Y
  have h:=(continuous_priceOfCoefficients_apply Y).tendsto c |>.comp hc
  simpa only [Function.comp_def,priceOfCoefficients_inverse] using h

end polyak.FiniteHorizon
