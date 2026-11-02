import krylov.Functions.PlanarValueDerivatives
import krylov.Functions.ValueFibreCoercivity

/-!
Article: main_krylov, prop:Fcycle(iii), unrestricted common-output localization.
Use: turn the actual nontrivial invisible cubic gradient into a global O(p)
enclosure for every common output having O(p³) gradients in both scenarios.
The output is arbitrary and is not assumed to lie in a local neighborhood.
Source: the exact four-coefficient value fibre and its proved homogeneous
quadratic gradient coercivity.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic

/-- The two actual differential coefficients of the exact hidden cubic.
Article: main_krylov, prop:Fcycle(iii). -/
def valueFibreCoordinateDerivative (d p r : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (d/2*z.2*(z.2-2*r*z.1+r*p),d/2*(z.1-p)*(2*z.2-r*z.1))

/-- The genuine linear part below the homogeneous quadratic hidden gradient.
Article: main_krylov, prop:Fcycle(iii), global output enclosure. -/
def valueFibreLinearDerivative (d r : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (d*r/2*z.2,d*r/2*z.1-d*z.2)

/-- The actual full hidden gradient is its homogeneous quadratic part plus
its p-scaled genuine linear part. Article: main_krylov, prop:Fcycle(iii). -/
theorem valueFibreCoordinateDerivative_decomposition (d p r : ℝ) (z : ℝ × ℝ) :
    valueFibreCoordinateDerivative d p r z=
      valueFibreHomogeneousGradient d r z+p • valueFibreLinearDerivative d r z := by
  ext <;> simp only [valueFibreCoordinateDerivative,valueFibreHomogeneousGradient,
    valueFibreLinearDerivative,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

/-- The actual hidden cubic's lower-degree gradient part has a uniform linear
bound. Article: main_krylov, prop:Fcycle(iii). -/
theorem valueFibreLinearDerivative_bound (d r : ℝ) (z : ℝ × ℝ) :
    ‖valueFibreLinearDerivative d r z‖≤|d| *(|r|+1)*‖z‖ := by
  have hx : |z.1|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hy : |z.2|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le z
  have hL : |d*r/2*z.2|≤|d| *|r|/2*‖z‖ := by
    rw [abs_mul,abs_div,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hR : |d*r/2*z.1-d*z.2|≤(|d| *|r|/2+|d|)*‖z‖ := by
    calc
      _ ≤ |d*r/2*z.1|+|d*z.2| := abs_sub _ _
      _ ≤ |d| *|r|/2*‖z‖+|d| *‖z‖ := by
        rw [abs_mul,abs_div,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hx (by positivity))
          (mul_le_mul_of_nonneg_left hy (abs_nonneg d))
      _ = _ := by ring
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  change max |d*r/2*z.2| |d*r/2*z.1-d*z.2|≤_
  have h₀ := mul_nonneg (abs_nonneg d) (norm_nonneg z)
  have h₁ := mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg r)) (norm_nonneg z)
  apply max_le
  · exact hL.trans (by nlinarith only [h₀,h₁])
  · exact hR.trans (by nlinarith only [h₁])

/-- The actual invisible cubic gradient controls every point globally, with
its exact p-dependent linear error. Article: main_krylov, prop:Fcycle(iii). -/
theorem valueFibreCoordinateDerivative_coercive (d r : ℝ) (hd : d≠0) (hr : r≠0) :
    ∃ c : ℝ, 0<c ∧ ∀ p : ℝ, ∀ z : ℝ × ℝ,
      c*‖z‖^2≤‖valueFibreCoordinateDerivative d p r z‖+|p| * (|d| *(|r|+1))*‖z‖ := by
  obtain ⟨c,hc,hbound⟩ := valueFibreHomogeneousGradient_coercive d r hd hr
  refine ⟨c,hc,?_⟩
  intro p z
  have he : valueFibreHomogeneousGradient d r z=
      valueFibreCoordinateDerivative d p r z-p • valueFibreLinearDerivative d r z := by
    rw [valueFibreCoordinateDerivative_decomposition,add_sub_cancel_right]
  have hn := hbound z
  rw [he] at hn
  calc
    _ ≤ ‖valueFibreCoordinateDerivative d p r z-p • valueFibreLinearDerivative d r z‖ := hn
    _ ≤ ‖valueFibreCoordinateDerivative d p r z‖+‖p • valueFibreLinearDerivative d r z‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_smul,Real.norm_eq_abs]
      have hh := mul_le_mul_of_nonneg_left (valueFibreLinearDerivative_bound d r z) (abs_nonneg p)
      nlinarith only [hh]

/-- The two true differential coordinates of the full actual planar family.
Article: main_krylov, prop:Fcycle(iii). -/
def planarValueCoordinateDerivative (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (z : ℝ × ℝ) : ℝ × ℝ :=
  (t.t0/2*z.1^2+t.t1*z.1*z.2+t.t2/2*z.2^2-t.t0*p/2*z.1-t.t1*p/2*z.2,
    t.t1/2*z.1^2+t.t2*z.1*z.2+t.t3/2*z.2^2-t.t1*p/2*z.1-t.t2*p*z.2-t.t3*r*p/2*z.2)

/-- Equal true observations give exactly the hidden cubic's actual full
coordinate-gradient difference, at every unrestricted point.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarValueCoordinateDerivative_difference (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (z : ℝ × ℝ) :
    planarValueCoordinateDerivative p r u z-planarValueCoordinateDerivative p r t z=
      valueFibreCoordinateDerivative (u.t2-t.t2) p r z := by
  have h0 : t.t0=u.t0 := congrArg Observation.t0 hobs
  have h3 : t.t3=u.t3 := congrArg Observation.t3 hobs
  have hP : t.t1+r*t.t2=u.t1+r*u.t2 := congrArg Observation.P hobs
  ext
  · simp only [planarValueCoordinateDerivative,valueFibreCoordinateDerivative,Prod.fst_sub]
    rw [h0]
    linear_combination -(z.1*z.2-p*z.2/2)*hP
  · simp only [planarValueCoordinateDerivative,valueFibreCoordinateDerivative,Prod.snd_sub]
    rw [h3]
    linear_combination -(z.1^2/2-p*z.1/2)*hP

/-- A global coercive quadratic inequality gives an actual linear shrinking
radius. Article: main_krylov, prop:Fcycle(iii), unrestricted-output bootstrap. -/
theorem quadratic_coercive_scale_bound (c A L p z : ℝ) (hc : 0<c) (hA : 0≤A)
    (hL : 0≤L) (hp : 0<p) (hp₁ : p≤1)
    (hb : c*z^2≤A*p^3+L*p*z) : z≤(1+(A+L+1)/c)*p := by
  by_contra hn
  have hbig : (1+(A+L+1)/c)*p<z := lt_of_not_ge hn
  have hM : 1≤1+(A+L+1)/c := le_add_of_nonneg_right (by positivity)
  have hpz : p<z := (by nlinarith only [hM,hp] : p≤(1+(A+L+1)/c)*p).trans_lt hbig
  have hcLarge : (A+L+1)*p<c*z := by
    have hdiv : c*(1+(A+L+1)/c)=c+A+L+1 := by field_simp; ring
    have hh := mul_lt_mul_of_pos_left hbig hc
    rw [←mul_assoc,hdiv] at hh
    nlinarith only [hh,mul_pos hc hp]
  have hprod := mul_lt_mul_of_pos_right hcLarge (hp.trans hpz)
  have hpp : A*p^3≤A*p^2 := by
    have hh := mul_le_mul_of_nonneg_left hp₁ (by positivity : 0≤A*p^2)
    nlinarith only [hh]
  have hAz : A*p^2≤A*p*z := by
    convert mul_le_mul_of_nonneg_left hpz.le (mul_nonneg hA hp.le) using 1; ring
  nlinarith only [hb,hprod,hpp,hAz,mul_pos hp (hp.trans hpz)]

/-- Every common output whose two actual cubic-scenario gradients are cubic
small lies in a derived O(p) ball, globally and without an output-domain
assumption. Article: main_krylov, prop:Fcycle(iii).
The common base field cancels exactly. -/
theorem planarValue_common_output_localization (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ base : (ℝ × ℝ) → ℝ × ℝ,
      ∀ z : ℝ × ℝ,
      ‖base z+planarValueCoordinateDerivative p r t z‖≤A*p^3 →
      ‖base z+planarValueCoordinateDerivative p r u z‖≤A*p^3 → ‖z‖≤C*p := by
  obtain ⟨c,hc,hcoercive⟩ := valueFibreCoordinateDerivative_coercive (u.t2-t.t2) r hd hr
  let L := |u.t2-t.t2| * (|r|+1)
  refine ⟨1+(2*A+L+1)/c,by dsimp only [L]; positivity,?_⟩
  intro p hp hp₁ base z ht hu
  have hdiff : ‖valueFibreCoordinateDerivative (u.t2-t.t2) p r z‖≤2*A*p^3 := by
    rw [←planarValueCoordinateDerivative_difference p r t u hobs z]
    have he : planarValueCoordinateDerivative p r u z-planarValueCoordinateDerivative p r t z=
        (base z+planarValueCoordinateDerivative p r u z)-(base z+planarValueCoordinateDerivative p r t z) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hu ht).trans_eq (by ring))
  have hb := hcoercive p z
  rw [abs_of_pos hp] at hb
  exact quadratic_coercive_scale_bound c (2*A) L p ‖z‖ hc (by positivity)
    (by dsimp only [L]; positivity) hp hp₁ (by
      dsimp only [L]
      nlinarith only [hb,hdiff])

/-- True differential coordinates in the two actual coordinate directions.
Article: main_krylov, prop:Fcycle(iii), actual scalar-function interpretation. -/
def planarDifferentialCoordinates (D : (ℝ × ℝ) →L[ℝ] ℝ) : ℝ × ℝ := (D (1,0),D (0,1))

/-- Both true differential coordinates are bounded by the actual differential
operator norm. Article: main_krylov, prop:Fcycle(iii). -/
theorem planarDifferentialCoordinates_norm (D : (ℝ × ℝ) →L[ℝ] ℝ) :
    ‖planarDifferentialCoordinates D‖≤‖D‖ := by
  rw [Prod.norm_def]
  apply max_le
  · simpa [planarDifferentialCoordinates,Prod.norm_def] using D.le_opNorm (1,0)
  · simpa [planarDifferentialCoordinates,Prod.norm_def] using D.le_opNorm (0,1)

/-- The displayed coordinate gradient is extracted from the genuine proved
Frechet differential of the actual full cubic function.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planarValueCoordinateDerivative_actual (p r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (z : ℝ × ℝ) : planarValueCoordinateDerivative p r t z=
    planarDifferentialCoordinates (planarValueDerivative
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p r t z) := by
  ext <;> simp [planarValueCoordinateDerivative,planarDifferentialCoordinates,planarValueDerivative]

/-- The unrestricted-output shrinking enclosure holds for the actual scalar
functions and their actual Frechet differentials, with any common smooth
base objective. Article: main_krylov, prop:Fcycle(iii).
This theorem supplies the first global localization step of the exact cubic
function information lower bound. -/
theorem planarValue_actual_common_output_localization (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0)
    (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ base : (ℝ × ℝ) → ℝ,
      ∀ z : ℝ × ℝ, DifferentiableAt ℝ base z →
      ‖fderiv ℝ (fun x=>base x+planarValueFamily (ContinuousLinearMap.fst ℝ ℝ ℝ)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p r t x) z‖≤A*p^3 →
      ‖fderiv ℝ (fun x=>base x+planarValueFamily (ContinuousLinearMap.fst ℝ ℝ ℝ)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p r u x) z‖≤A*p^3 → ‖z‖≤C*p := by
  obtain ⟨C,hC,hbound⟩ := planarValue_common_output_localization r t u hobs hd hr A hA
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ base z hbase ht hu
  let B := fun z=>planarDifferentialCoordinates (fderiv ℝ base z)
  have hcoord (w : krylov.Tensor.BinaryCubic)
      (hw : ‖fderiv ℝ (fun x=>base x+planarValueFamily (ContinuousLinearMap.fst ℝ ℝ ℝ)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p r w x) z‖≤A*p^3) :
      ‖B z+planarValueCoordinateDerivative p r w z‖≤A*p^3 := by
    have hd := (hbase.hasFDerivAt.add (planarValueFamily_hasFDerivAt
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p r w z)).fderiv
    change fderiv ℝ (fun x=>base x+planarValueFamily (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p r w x) z=_ at hd
    have he : B z+planarValueCoordinateDerivative p r w z=
        planarDifferentialCoordinates (fderiv ℝ (fun x=>base x+planarValueFamily
          (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p r w x) z) := by
      rw [hd,planarValueCoordinateDerivative_actual]
      rfl
    rw [he]
    exact (planarDifferentialCoordinates_norm _).trans hw
  exact hbound p hp hp₁ B z (hcoord t ht) (hcoord u hu)

end
end krylov.Functions
