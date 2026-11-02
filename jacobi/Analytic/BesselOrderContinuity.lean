import jacobi.Analytic.BesselOrder

/-!
Article: jacobi, Lemma E.1.
The genuine normalized Bessel function is jointly continuous in complex
order and spectral argument, on the complete original order half-plane.
The proof gives an actual common series majorant on a product neighborhood.
This is the continuity input for finite spectral contours; uniform
large-index root control still requires the complex Hankel remainder.
Use: normalized_order_spectral_continuous justifies perturbing both genuine source parameters on one neighborhood.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Real Set Filter
open scoped Topology

/-- The actual original Bessel series has a common summable majorant whenever the order has positive real-part margin and the spectral argument is bounded.
Use: normalized_order_spectral_continuous justifies perturbing both genuine source parameters on one neighborhood.
Article: jacobi, Lemma E.1.
Proof: multiply the proved factorial coefficient bound by |z|^n and use
the genuine spectral-radius bound, preserving its exponential majorant. -/
theorem normalized_joint_majorant {δ R:ℝ} (hδ:0<δ) {a z:ℂ}
    (ha:δ≤a.re+1) (hz:‖z‖≤R) (n:ℕ) :
    ‖coefficient a n*z^n‖≤(R/(4*δ))^n/(n.factorial:ℝ) := by
  rw [norm_mul,norm_pow]
  calc
    _≤((1/(4*δ))^n/(n.factorial:ℝ))*R^n :=
      mul_le_mul (coefficient_order_bound hδ ha n) (pow_le_pow_left₀ (norm_nonneg _) hz n)
        (by positivity) (by positivity)
    _=_ := by rw [div_mul_eq_mul_div,← mul_pow]; congr 2; ring

/-- The actual normalized Bessel function is jointly continuous in its complex order and original spectral coordinate.
Use:, 's finite root contours can be kept free of zeros under a genuine small order perturbation of the same source Bessel function.
Article: jacobi, Lemma E.1.
Source: the Weierstrass majorant theorem for uniformly convergent series.
Proof: around each original pair keep half the order margin and a spectral
radius larger than its norm. The common actual factorial majorant is
summable and every original coefficient term is continuous there. The
true uniformly convergent sum is therefore continuous on that neighborhood. -/
theorem normalized_order_spectral_continuous :
    ContinuousOn (fun p:ℂ × ℂ => normalized p.1 p.2) {p | -1<p.1.re} := by
  -- Both variables vary on one genuine product neighborhood, before passing to the original series sum.
  intro p hp
  change -1<p.1.re at hp
  let δ : ℝ := (p.1.re+1)/2
  let R : ℝ := ‖p.2‖+1
  have hδ : 0<δ := by dsimp [δ]; linarith
  let U : Set (ℂ × ℂ) := {q | δ<q.1.re+1 ∧ ‖q.2‖<R}
  have hU : IsOpen U := (isOpen_lt continuous_const
    ((Complex.continuous_re.comp continuous_fst).add_const 1)).inter
      (isOpen_lt continuous_snd.norm continuous_const)
  have hpU : p∈U := by dsimp [U,δ,R]; constructor <;> linarith
  have hterms (n:ℕ) : ContinuousOn (fun q:ℂ × ℂ => coefficient q.1 n*q.2^n) U := by
    intro q hq
    have hqa : -1<q.1.re := by have hh := hq.1; linarith
    exact (((coefficient_order_analytic hqa n).continuousAt.comp continuous_fst.continuousAt).mul
      (continuous_snd.continuousAt.pow n)).continuousWithinAt
  have hmaj (n:ℕ) (q:ℂ × ℂ) (hq:q∈U) :
      ‖coefficient q.1 n*q.2^n‖≤(R/(4*δ))^n/(n.factorial:ℝ) :=
    normalized_joint_majorant hδ hq.1.le hq.2.le n
  have hu := tendstoUniformlyOn_tsum (Real.summable_pow_div_factorial (R/(4*δ))) hmaj
  have hc : ContinuousOn (fun q:ℂ × ℂ => ∑'n,coefficient q.1 n*q.2^n) U := by
    apply hu.continuousOn (Filter.Eventually.frequently (Eventually.of_forall (fun s => ?_)))
    exact continuousOn_finsetSum _ (fun n _ => hterms n)
  simp_rw [← normalized_eq_tsum] at hc
  exact (hc.continuousAt (hU.mem_nhds hpU)).continuousWithinAt

end
end jacobi.Bessel
