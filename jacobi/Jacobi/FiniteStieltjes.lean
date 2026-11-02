import jacobi.Bessel.NegativeAxis
import jacobi.Jacobi.FiniteMoments

/-!
Article: jacobi, Lemma 1.3.
The actual finite Jacobi resolvent sum equals the genuine logarithmic
derivative of the same scaled finite polynomial. Its limit is the actual
Bessel logarithmic derivative, which is nonnegative and decreasing.
Source: actual polynomial logarithmic derivatives and the proved derivative Mehler--Heine limit.
Use: identifies the Bessel logarithmic derivative and detects any missing first trace.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual finite Stieltjes resolvent sum over the complete source scaled spectrum.
Use: identifies the Bessel logarithmic derivative and detects any missing first trace.
Article: jacobi, Lemma 1.3.
-/
def finiteStieltjes (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i:Fin n,finiteLambda a b ha hb n i/(1+s*finiteLambda a b ha hb n i)

/-- Every actual finite Stieltjes sum is nonnegative on the nonnegative parameter axis.
Use: its genuine limiting Bessel logarithmic derivative is nonnegative.
Article: jacobi, Lemma 1.3.
Proof: each actual finite eigenvalue is nonnegative and its resolvent denominator is at least one. -/
theorem finiteStieltjes_nonneg {a b s : ℝ} (ha : -1<a) (hb : -1<b)
    (n : ℕ) (hs : 0≤s) : 0≤finiteStieltjes a b ha hb n s := by
  unfold finiteStieltjes
  apply Finset.sum_nonneg
  intro i _
  have hn : 0<n := by have hi := i.isLt; omega
  have hLambda : 0≤finiteLambda a b ha hb n i := div_nonneg (by norm_num) ((finiteSigma_properties ha hb hn).1 i).le
  exact div_nonneg hLambda (by nlinarith [mul_nonneg hs hLambda])

/-- The genuine finite Stieltjes sum is decreasing on the nonnegative axis.
Use: proves monotonicity of the actual limiting Bessel logarithmic derivative without an assumed infinite product identity.
Article: jacobi, Lemma 1.3.
Proof: increasing the parameter increases every positive resolvent denominator, so each genuine nonnegative summand decreases. -/
theorem finiteStieltjes_antitone {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    AntitoneOn (finiteStieltjes a b ha hb n) (Ici (0:ℝ)) := by
  intro s hs t _ hst
  unfold finiteStieltjes
  apply Finset.sum_le_sum
  intro i _
  have hn : 0<n := by have hi := i.isLt; omega
  have hLambda : 0≤finiteLambda a b ha hb n i := div_nonneg (by norm_num) ((finiteSigma_properties ha hb hn).1 i).le
  exact div_le_div_of_nonneg_left hLambda (by nlinarith [mul_nonneg hs hLambda]) (by nlinarith)

/-- The actual finite Stieltjes sum is the genuine logarithmic derivative of its original negative-axis Jacobi function.
Use: taking the proved derivative Mehler--Heine limit identifies the actual Bessel Stieltjes function.
Article: jacobi, Lemma 1.3.
Proof: apply the actual polynomial logarithmic derivative at the negative
shifted coordinate. The true polynomial value is at least one. Its
ordinary chain factors and each nonzero positive finite spectral scale
convert the actual reciprocal-root terms into the exact resolvent summands. -/
theorem finiteStieltjes_log_derivative {a b s : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (hs : 0≤s) :
    finiteStieltjes a b ha hb n s=
      (-2*scaledRealSlope a b n (-2*s))/scaledReal a b n (-2*s) := by
  -- Every denominator is justified by the actual finite spectrum and the genuine positive polynomial value.
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  let u : ℝ := (-2*s)/(4*(n:ℝ)^2)
  have hp : (shiftedPolynomial a b n).eval u≠0 := by
    have h := scaledReal_negative_ge_one ha hb hn hs
    rw [scaledReal_eq_shifted] at h
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h)
  have hlog := shifted_logarithmic_derivative ha hb n hp
  rw [scaledReal_eq_shifted]
  unfold scaledRealSlope
  change (∑ i:Fin n,finiteLambda a b ha hb n i/(1+s*finiteLambda a b ha hb n i))=
    (-2*((shiftedPolynomial a b n).derivative.eval u/(4*(n:ℝ)^2)))/(shiftedPolynomial a b n).eval u
  rw [show (-2*((shiftedPolynomial a b n).derivative.eval u/(4*(n:ℝ)^2)))/(shiftedPolynomial a b n).eval u=
      (-1/(2*(n:ℝ)^2))*((shiftedPolynomial a b n).derivative.eval u/(shiftedPolynomial a b n).eval u) by ring,
    hlog,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let r := shiftedRoots a b ha hb n i
  have hr : 0<r := (shiftedRoots_properties ha hb i).2.1
  have hLambda : finiteLambda a b ha hb n i=1/(2*(n:ℝ)^2*r) := by rw [finiteLambda_shifted ha hb i]; ring
  have hd : 0<2*(n:ℝ)^2*r+s := by nlinarith [sq_pos_of_ne_zero hnR]
  have hden : u-shiftedRoots a b ha hb n i= -(2*(n:ℝ)^2*r+s)/(2*(n:ℝ)^2) := by
    dsimp only [u,r]
    field_simp [hnR]
    ring
  rw [hLambda,hden]
  field_simp [hnR,hr.ne',hd.ne']

/-- The actual finite Stieltjes sums converge to the genuine original Bessel logarithmic derivative at every nonnegative parameter.
Use: proves the actual limiting Stieltjes geometry before identifying the first infinite Rayleigh sum.
Article: jacobi, Lemma 1.3.
Proof: the actual finite value and actual finite derivative converge by
Mehler--Heine and its community differentiation theorem. The limiting
Bessel value is at least one, so their true quotient converges. -/
theorem finiteStieltjes_tendsto {a b s : ℝ} (ha : -1<a) (hb : -1<b) (hs : 0≤s) :
    Tendsto (fun n : ℕ => finiteStieltjes a b ha hb n s) atTop (𝓝 (jacobi.Bessel.stieltjes a s)) := by
  have h := ((scaledRealSlope_tendsto (b := b) ha (-2*s)).const_mul (-2)).div
    (scaledReal_tendsto (b := b) ha (-2*s))
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (jacobi.Bessel.negativeValue_ge_one ha hs)))
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact finiteStieltjes_log_derivative ha hb hn hs

end
end jacobi.Jacobi

namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology

/-- The original Bessel Stieltjes function is nonnegative on the entire nonnegative axis.
Use: its actual Riccati equation forces decay and rules out a hidden first-trace defect.
Article: jacobi, Lemma 1.3.
Proof: choose the genuine Jacobi approximation with beta=0 and pass the proved finite nonnegativity to its actual Bessel logarithmic-derivative limit. -/
theorem stieltjes_nonneg {a s : ℝ} (ha : -1<a) (hs : 0≤s) : 0≤stieltjes a s := by
  have hb : (-1:ℝ)<0 := by norm_num
  exact ge_of_tendsto (jacobi.Jacobi.finiteStieltjes_tendsto ha hb hs)
    (Eventually.of_forall (fun n => jacobi.Jacobi.finiteStieltjes_nonneg ha hb n hs))

/-- The actual Bessel Stieltjes function decreases on the nonnegative axis.
Use: converts an eventual positive lower bound into a global tail contradiction with the genuine Riccati equation.
Article: jacobi, Lemma 1.3.
Proof: pass the actual finite Stieltjes comparison to the two genuine quotient limits. -/
theorem stieltjes_antitone {a : ℝ} (ha : -1<a) : AntitoneOn (stieltjes a) (Ici (0:ℝ)) := by
  intro s hs t ht hst
  have hb : (-1:ℝ)<0 := by norm_num
  exact le_of_tendsto_of_tendsto (jacobi.Jacobi.finiteStieltjes_tendsto ha hb ht)
    (jacobi.Jacobi.finiteStieltjes_tendsto ha hb hs)
    (Eventually.of_forall (fun n => jacobi.Jacobi.finiteStieltjes_antitone ha hb n hs ht hst))

end
end jacobi.Bessel
