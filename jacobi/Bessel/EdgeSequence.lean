import jacobi.Bessel.Enumeration
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Article: jacobi, Proposition C.4.
The classical positive-axis Bessel function is defined by its actual
normalized entire series. The complete increasing zero list gives genuine
j_(alpha,k), sigma_k and Lambda_k, with positivity, order and endpoint limits.
Source: DLMF 10.2.2, the defining Bessel series with its Gamma normalization.
The Rayleigh sums and canonical product are separate statements, not assumptions here.
Use: identifies the source zeros of J_alpha with the actual entire spectral zeros already constructed.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The classical real Bessel function on the positive axis, realized by its genuine normalized entire series.
Use: identifies the source zeros of J_alpha with the actual entire spectral zeros already constructed.
Article: jacobi, Proposition C.4.
-/
def cylindrical (a x : ℝ) : ℝ := (x/2)^a/Real.Gamma (a+1)*realNormalized a (x^2)

/-- The positive Bessel zeros, indexed from zero instead of the source's one.
Use: supplies j_(alpha,n+1) with no assumed zero enumeration.
Article: jacobi, Lemma 1.3.
-/
def positiveZero (a : ℝ) (ha : -1<a) (n : ℕ) : ℝ := √(sigma a ha n)

/-- The actual Bessel edge eigenvalue sequence.
Use: supplies the positive decreasing Lambda_k in later spectral identifications.
Article: jacobi, Lemma E.1.
-/
def edgeValue (a : ℝ) (ha : -1<a) (n : ℕ) : ℝ := 2/sigma a ha n

/-- On the positive axis the classical Bessel function has exactly the normalized entire spectral zeros.
Use: identifies the constructed squared-zero enumeration with the article's actual J_alpha zeros.
Article: jacobi, Proposition C.4.
Proof: the real-power prefactor is positive and Gamma(alpha+1) is
positive in the full stated order range, so both normalizations are nonzero. -/
theorem cylindrical_zero_iff {a x : ℝ} (ha : -1<a) (hx : 0<x) :
    cylindrical a x=0 ↔ normalized (a:ℂ) ((x^2:ℝ):ℂ)=0 := by
  have hG : 0<Real.Gamma (a+1) := Real.Gamma_pos_of_pos (by linarith)
  rw [cylindrical,mul_eq_zero,or_iff_right (ne_of_gt (div_pos
    (Real.rpow_pos_of_pos (by positivity : 0<x/2) _) hG)),realNormalized_zero_iff]

/-- Every constructed positive Bessel zero is strictly positive and its square is the enumerated spectral zero.
Use: permits switching freely between j and sigma in the source's edge statements.
Article: jacobi, Proposition B.1.
Proof: every enumerated actual spectral zero is positive; apply the
genuine square-root positivity and squared-square-root identities. -/
theorem positiveZero_properties {a : ℝ} (ha : -1<a) (n : ℕ) :
    0<positiveZero a ha n ∧ (positiveZero a ha n)^2=sigma a ha n := by
  have hp := spectralZero_pos ha (sigma_mem ha n)
  exact ⟨Real.sqrt_pos.mpr hp,Real.sq_sqrt hp.le⟩

/-- Every constructed j is a genuine positive zero of the classical Bessel function.
Use: verifies that the source sequence contains only actual Bessel zeros.
Article: jacobi, Proposition B.1.
Proof: its square is the actual enumerated entire-function zero and the positive-axis normalization is nonzero. -/
theorem positiveZero_is_zero {a : ℝ} (ha : -1<a) (n : ℕ) :
    cylindrical a (positiveZero a ha n)=0 := by
  rw [cylindrical_zero_iff ha (positiveZero_properties ha n).1,(positiveZero_properties ha n).2]
  exact sigma_mem ha n

/-- The genuine positive Bessel zeros are strictly increasing.
Use: fixes the article's canonical ordering j_(alpha,1)<j_(alpha,2)<... .
Article: jacobi, Lemma E.1.
Proof: the strictly increasing positive squared zeros remain strictly increasing under square root. -/
theorem positiveZero_strictMono {a : ℝ} (ha : -1<a) : StrictMono (positiveZero a ha) := by
  intro m n hmn
  exact Real.sqrt_lt_sqrt (spectralZero_pos ha (sigma_mem ha m)).le (sigma_strictMono ha hmn)

/-- Every positive zero of the classical Bessel function occurs in the constructed sequence.
Use: the source j list exhausts the actual positive-axis zero set.
Article: jacobi, Lemma 1.3.
Proof: its positive square is an actual spectral zero, hence an enumerated sigma.
The positive square root then recovers the original positive argument. -/
theorem positiveZero_exhaustive {a x : ℝ} (ha : -1<a) (hx : 0<x)
    (hz : cylindrical a x=0) : ∃ n,positiveZero a ha n=x := by
  obtain ⟨n,hn⟩ := sigma_exhaustive ha ((cylindrical_zero_iff ha hx).mp hz)
  refine ⟨n,?_⟩
  rw [positiveZero,hn,Real.sqrt_sq hx.le]

/-- Every genuine Bessel edge value is positive, and the sequence strictly decreases.
Use: supplies the ordered positive eigenvalue geometry before proving its Rayleigh sums.
Article: jacobi, Proposition B.1.
Proof: all squared zeros are positive and strictly increase, so their positive reciprocal multiples strictly decrease. -/
theorem edgeValue_properties {a : ℝ} (ha : -1<a) :
    (∀ n,0<edgeValue a ha n) ∧ StrictAnti (edgeValue a ha) := by
  refine ⟨fun n => div_pos (by norm_num) (spectralZero_pos ha (sigma_mem ha n)),?_⟩
  intro m n hmn
  exact div_lt_div_of_pos_left (by norm_num) (spectralZero_pos ha (sigma_mem ha m)) (sigma_strictMono ha hmn)

/-- The genuine positive Bessel zeros tend to infinity.
Use: the source large-zero asymptotics concern an actual exhaustive unbounded sequence.
Article: jacobi, Lemma E.1.
Proof: square root tends to infinity and the actual squared zeros already have that filter limit. -/
theorem positiveZero_tendsto {a : ℝ} (ha : -1<a) : Tendsto (positiveZero a ha) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (sigma_tendsto ha)

/-- The genuine Bessel edge eigenvalues tend to zero.
Use: verifies the elementary compact-spectrum endpoint behavior without assuming summability.
Article: jacobi, Lemma E.1.
Proof: the squared zeros tend to infinity, hence their reciprocals tend to zero; multiply by two. -/
theorem edgeValue_tendsto {a : ℝ} (ha : -1<a) :
    Tendsto (edgeValue a ha) atTop (𝓝 0) := by
  change Tendsto (fun n => 2/sigma a ha n) atTop (𝓝 0)
  simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using
    (tendsto_inv_atTop_zero.comp (sigma_tendsto ha)).const_mul 2

end
end jacobi.Bessel
