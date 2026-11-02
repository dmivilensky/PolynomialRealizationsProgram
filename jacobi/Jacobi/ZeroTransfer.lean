import jacobi.Jacobi.Real
import jacobi.Jacobi.MehlerHeine
import jacobi.Bessel.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Lemma 1.3.
Every genuine simple Bessel spectral zero is approached by actual real
zeros of the finite scaled Jacobi polynomials. The proof uses the proved
Mehler--Heine limit, actual realness and the intermediate value theorem.
It does not assume a Hurwitz theorem or an ordered finite zero list.
Source: stability of real sign-changing zeros under locally uniform convergence.
Use: formulates convergence and zero transfer in the source spectral variable sigma.
-/
namespace jacobi.Jacobi
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine real finite Jacobi polynomial at its squared edge scaling.
Use: formulates convergence and zero transfer in the source spectral variable sigma.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def scaledReal (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  realNormalized a b n (1-x/(2*(n:ℝ)^2))

/-- Every actual scaled finite Jacobi polynomial is continuous on the full real spectral axis.
Use: the finite-zero transfer has no missing interval-continuity premise.
Article: jacobi, Lemma 1.3.
Proof: compose the actual real polynomial with its continuous affine spectral scaling. -/
theorem scaledReal_continuous (a b : ℝ) (n : ℕ) : Continuous (scaledReal a b n) :=
  (realNormalized_continuous a b n).comp (continuous_const.sub (continuous_id.div_const _))

/-- The actual finite Jacobi values converge to the actual real normalized Bessel value at every real spectral point.
Use: preserves the two strict signs around every genuine simple Bessel zero.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: specialize the full uniform complex limit to one point and take
its continuous real part. Real-field casts give exactly the original finite scaling. -/
theorem scaledReal_tendsto {a b : ℝ} (ha : -1<a) (x : ℝ) :
    Tendsto (fun n => scaledReal a b n x) atTop (𝓝 (jacobi.Bessel.realNormalized a x)) := by
  -- The limit is the same actual normalized Bessel function used in the zero theory.
  have h := (mehler_heine_uniform (a := (a:ℂ)) (b := (b:ℂ)) (by simpa using ha)
    (R := |x|) (abs_nonneg x)).tendsto_at (x := (x:ℂ)) (by
      simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,le_refl])
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp h
  have he (n : ℕ) : (1-(x:ℂ)/(2*(n:ℂ)^2))=((1-x/(2*(n:ℝ)^2):ℝ):ℂ) := by
    push_cast
    rfl
  simpa only [Function.comp_def,he,scaledReal,realNormalized,jacobi.Bessel.realNormalized] using hRe

/-- Every genuine Bessel spectral zero is approximated by actual real finite Jacobi zeros at all sufficiently large degrees.
Use: provides the existence half of the source finite-edge zero convergence, independently of ordered zero counting.
Article: jacobi, Lemma 1.3.
Proof: the actual simple real Bessel zero has opposite-sign values
inside every prescribed neighborhood. Mehler--Heine preserves those two
strict signs eventually. The intermediate value theorem supplies a true
finite Jacobi zero between the two points, still inside that neighborhood. -/
theorem scaled_zero_approximation {a b x ε : ℝ} (ha : -1<a)
    (hx : jacobi.Bessel.normalized (a:ℂ) (x:ℂ)=0) (hε : 0<ε) :
    ∀ᶠ n:ℕ in atTop,∃ z:ℝ,|z-x|<ε ∧
      normalized (a:ℂ) (b:ℂ) n ((1-z/(2*(n:ℝ)^2):ℝ):ℂ)=0 := by
  -- Both signs belong to the same original Bessel function, and the finite zeros belong to the original Jacobi polynomial.
  obtain ⟨⟨u,hu,huneg⟩,⟨v,hv,hvpos⟩⟩ := jacobi.Bessel.realNormalized_signs ha hx hε
  have huN := (scaledReal_tendsto (b := b) ha u).eventually (Iio_mem_nhds huneg)
  have hvN := (scaledReal_tendsto (b := b) ha v).eventually (Ioi_mem_nhds hvpos)
  filter_upwards [huN,hvN] with n hnU hnV
  have hzero : (0:ℝ)∈uIcc (scaledReal a b n u) (scaledReal a b n v) :=
    Icc_subset_uIcc ⟨hnU.le,hnV.le⟩
  obtain ⟨z,hz,hval⟩ := intermediate_value_uIcc (scaledReal_continuous a b n).continuousOn hzero
  have hnear := ordConnected_Ioo.uIcc_subset hu hv hz
  refine ⟨z,?_,(realNormalized_zero_iff a b _ n).mp hval⟩
  exact abs_lt.mpr ⟨by linarith [hnear.1],by linarith [hnear.2]⟩

end
end jacobi.Jacobi
