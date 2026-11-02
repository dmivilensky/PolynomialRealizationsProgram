import jacobi.RootMass.VariationCalculus
import jacobi.Young.RadialPotential

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Finite-interval replacements have an explicit L1 bound. The existing exact
spectral expansion then has zero right-derivative remainder. Actual Lebesgue
primitive derivatives identify the linear term, so the spectral needle
formula is proved for the original compact positive operator.
Source: the isospectral quadratic expansion, Lebesgue differentiation and little-o calculus.
Use: supplies a genuine density to the spectral constraint and the minimizing property at every admissible needle width.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual nonnegative-width interval replacement, also defined harmlessly at negative widths.
Use: supplies a genuine density to the spectral constraint and the minimizing property at every admissible needle width.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
-/
def RootDensity.needle (m : RootDensity) (z : ℝ) (hz : 0≤z) (x eps : ℝ) : RootDensity :=
  m.replace (s := Ioc x (x+eps)) measurableSet_Ioc (by simp) z hz

/-- A zero-width actual needle has exactly its original pointwise density.
Use: identifies every spectral and integral base value in the localized variation.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the zero-width half-open interval is empty. -/
theorem RootDensity.needle_zero_value (m : RootDensity) (z : ℝ) (hz : 0≤z) (x : ℝ) :
    (m.needle z hz x 0).value=m.value := splice_zero_interval m.value z x

/-- The signed replacement difference is exactly its supported indicator.
Use: proves both the L1 needle estimate and the localized actual Green pairing.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: check separately whether the actual point belongs to the replacement set. -/
theorem splice_difference (s : Set ℝ) (m : ℝ → ℝ) (z : ℝ) :
    splice s m z-m=s.indicator (fun t => z-m t) := by
  classical
  funext t
  by_cases ht : t∈s <;> simp [splice,ht]

/-- The genuine L1 distance of a right needle has the source's first-order primitive bound.
Use: makes its actual quadratic spectral remainder little-o of the replacement width.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the signed difference is supported on the actual needle interval.
There |z-m|<=z+m. Integrate and identify the positive-width interval primitive. -/
theorem RootDensity.needle_distance (m : RootDensity) (z : ℝ) (hz : 0≤z) (x eps : ℝ) (heps : 0≤eps) :
    (∫ t,|(m.needle z hz x eps).value t-m.value t|)≤z*eps+∫ t in x..x+eps,m.value t := by
  -- The bound uses the actual original density's interval integral, so the Lebesgue derivative applies directly.
  let B := Ioc x (x+eps)
  have hd : IntegrableOn (fun t => z-m.value t) B := (integrableOn_const (by simp [B])).sub m.integrable.integrableOn
  have hc : IntegrableOn (fun t => z+m.value t) B := (integrableOn_const (by simp [B])).add m.integrable.integrableOn
  have he : (fun t => |(m.needle z hz x eps).value t-m.value t|)=B.indicator (fun t => |z-m.value t|) := by
    classical
    funext t
    by_cases ht : t∈B <;> simp [RootDensity.needle,RootDensity.replace,splice,B] at ht ⊢ <;> simp_all
  rw [he,integral_indicator measurableSet_Ioc]
  have hi := integral_mono hd.abs hc (fun t => abs_sub_le_iff.mpr
    ⟨by linarith [m.nonneg t],by linarith [m.nonneg t]⟩)
  have hsplit := integral_add (integrableOn_const (C := z) (s := B) (by simp [B])) m.integrable.integrableOn
  rw [hsplit,setIntegral_const,Measure.real,Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith : 0≤x+eps-x),smul_eq_mul] at hi
  have hmI : (∫ t in B,m.value t)=∫ t in x..x+eps,m.value t :=
    (intervalIntegral.integral_of_le (by linarith : x≤x+eps)).symm
  rw [hmI] at hi
  nlinarith

/-- The actual linear spectral pairing of a needle is its exact localized Green integral.
Use: the true spectral derivative is identified at common Lebesgue points of m and m*W_2.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the genuine signed second pairing equals its actual convolution
pairing by Fubini. The signed density difference is the proved needle indicator. -/
theorem RootDensity.needle_pairing (m : RootDensity) (z : ℝ) (hz : 0≤z) (x eps : ℝ) :
    secondPairing m.value ((m.needle z hz x eps).value-m.value)=
      ∫ t in Ioc x (x+eps),(z-m.value t)*potential m.toDensity t := by
  -- Every use of Fubini is supported by the existing signed L1 integrability theorem.
  let q := m.needle z hz x eps
  rw [secondPairing_symm m.integrable (q.integrable.sub m.integrable) m.measurable (q.measurable.sub m.measurable),
    secondPairing_iterated (q.integrable.sub m.integrable) m.integrable (q.measurable.sub m.measurable) m.measurable]
  simp_rw [← potential_kernel m.toDensity]
  have he : (fun t => (q.value-m.value) t*potential m.toDensity t)=
      (Ioc x (x+eps)).indicator (fun t => (z-m.value t)*potential m.toDensity t) := by
    classical
    funext t
    by_cases ht : t∈Ioc x (x+eps) <;> simp [q,RootDensity.needle,RootDensity.replace,splice,ht]
  rw [he,integral_indicator measurableSet_Ioc]

/-- A genuine Lebesgue primitive derivative at x gives its translated zero-width derivative.
Use: all needle cost and spectral formulas share this exact actual interval primitive.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: compose the actual primitive with the affine endpoint x+epsilon. -/
theorem translated_primitive_derivative {F : ℝ → ℝ} {x : ℝ}
    (hF : HasDerivAt (fun v => ∫ t in x..v,F t) (F x) x) :
    HasDerivAt (fun eps => ∫ t in x..x+eps,F t) (F x) 0 := by
  have hF' : HasDerivAt (fun v => ∫ t in x..v,F t) (F x) (x+0) := by simpa only [add_zero] using hF
  simpa only [Function.comp_def,id_eq,mul_one] using hF'.comp 0 ((hasDerivAt_id 0).const_add x)

/-- The true observable integral of a right needle has the exact Lebesgue first variation.
Use: proves localized mass, energy and root-mass derivatives for the same original density.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the exact finite-interval replacement identity agrees on the
admissible half-line with a differentiated affine term minus the actual Lebesgue primitive. -/
theorem RootDensity.needle_observable_derivative (m : RootDensity) (z : ℝ) (hz : 0≤z) (x : ℝ)
    (F : ℝ → ℝ) (hi : Integrable (fun t => F (m.value t)))
    (hF : HasDerivAt (fun v => ∫ t in x..v,F (m.value t)) (F (m.value x)) x) :
    HasDerivWithinAt (fun eps => ∫ t,F ((m.needle z hz x eps).value t))
      (F z-F (m.value x)) (Ici (0:ℝ)) 0 := by
  have hd := ((hasDerivAt_const 0 (∫ t,F (m.value t))).add
    ((hasDerivAt_id 0).mul_const (F z))).sub (translated_primitive_derivative hF)
  simp only [zero_add,one_mul] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact splice_interval_integral hi z x eps heps

end
end jacobi.RootMass
