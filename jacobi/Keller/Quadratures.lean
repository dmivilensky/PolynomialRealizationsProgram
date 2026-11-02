import jacobi.Keller.Weights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
Article: jacobi, Theorem D.6.
The printed j_k(c) are identified with the compact-parameter integrals by
an exact square-root rescaling. Genuine primitives evaluate all transition
values and the limiting mass value; no numerical integration is involved.
Source: the absolutely convergent quadratures and the real fundamental theorem of calculus.
Use: identifies the printed j integrals with the proved convergent compact-parameter quadratures.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Exact pointwise rescaling of the printed Keller integrand, valid even at its zero-denominator endpoint representative.
Use: identifies the printed j integrals with the proved convergent compact-parameter quadratures.
Article: jacobi, Theorem D.6.
Proof: the original polynomial equals c*P(1/c,v); positive square-root multiplicativity cancels sqrt(c). -/
theorem weight_rescale (k : ℕ) {c : ℝ} (hc : 0<c) (v : ℝ) :
    sqrt c*((1-v^2)^k/sqrt ((1-v^2/c)*(c*A v-1)))=weight k c⁻¹ v := by
  have hp : (1-v^2/c)*(c*A v-1)=c*P c⁻¹ v := by unfold P; field_simp
  rw [hp,Real.sqrt_mul hc.le,← mul_div_assoc,
    mul_div_mul_left _ _ (sqrt_pos.mpr hc).ne']
  rfl

/-- The actual printed Keller quadratures have the exact compact-parameter normalization.
Use: transfers endpoint evaluations, continuity and monotonicity to the source's original c parameter.
Article: jacobi, Theorem D.6.
Proof: move the constant inside the genuine interval integral and apply the pointwise rescaling. -/
theorem j_rescale (k : ℕ) {c : ℝ} (hc : 0<c) : sqrt c*j k c=J k c⁻¹ := by
  rw [j,J,← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun v _ => weight_rescale k hc v

/-- The transition integrand simplifies to an elementary square-root weight on the open unit interval.
Use: its true primitives give j_1(1), j_2(1) and j_3(1).
Article: jacobi, Theorem D.6.
Proof: factor P(1,v)=(1-v²)²*(2-v²) and cancel the positive factor 1-v². -/
theorem weight_one {k : ℕ} (hk : 1≤k) {v : ℝ} (hv : v∈Ioo (0:ℝ) 1) :
    weight k 1 v=(1-v^2)^(k-1)/sqrt (2-v^2) := by
  have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  have ha : 0<1-v^2 := sub_pos.mpr hv2
  have hP : P 1 v=(1-v^2)^2*(2-v^2) := by unfold P A; ring
  rw [weight,hP,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq ha.le]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [Nat.add_sub_cancel_left,pow_add,pow_one]
  exact mul_div_mul_left _ _ ha.ne'

/-- The elementary angular primitive has the exact transition weight as derivative.
Use: evaluates the two Keller endpoint integrals containing Real.pi.
Article: jacobi, Theorem D.6.
Proof: the arcsine chain rule and sqrt((2-v²)/2)=sqrt(2-v²)/sqrt(2) cancel the scaling. -/
theorem angle_derivative {v : ℝ} (hv : v∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun x => arcsin (x/sqrt 2)) (1/sqrt (2-v^2)) v := by
  -- Strict interior inequalities discharge the arcsine and square-root derivative conditions.
  have hs : 0<sqrt (2:ℝ) := sqrt_pos.mpr (by norm_num)
  have hs2 : sqrt (2:ℝ)^2=2 := sq_sqrt (by norm_num)
  have hs1 : 1<sqrt (2:ℝ) := by nlinarith [sqrt_nonneg (2:ℝ)]
  have hvarg : 0<v/sqrt 2 := div_pos hv.1 hs
  have hvlt : v/sqrt 2<1 := (div_lt_one hs).mpr (hv.2.trans hs1)
  have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  have hp : 0<2-v^2 := by linarith
  have hh := (hasDerivAt_arcsin (by linarith : v/sqrt 2≠-1) hvlt.ne).comp v
    ((hasDerivAt_id v).div_const (sqrt 2))
  dsimp only [id_eq,Function.comp_def] at hh
  convert! hh using 1
  have he : 1-(v/sqrt 2)^2=(2-v^2)/2 := by field_simp; nlinarith [hs2]
  rw [he,Real.sqrt_div hp.le]
  field_simp [hs.ne',(sqrt_pos.mpr hp).ne']

/-- The exact transition angle at the upper endpoint is Real.pi/4.
Use: evaluates j_1(1) and j_3(1) in the original source normalization.
Article: jacobi, Theorem D.6.
Proof: the argument equals sin(Real.pi/4); use the principal arcsine branch. -/
theorem angle_one : arcsin (1/sqrt (2:ℝ))=Real.pi/4 := by
  have hs : 0<sqrt (2:ℝ) := sqrt_pos.mpr (by norm_num)
  have he : 1/sqrt (2:ℝ)=sqrt 2/2 := by field_simp; nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [he,← sin_pi_div_four,arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

/-- All three Keller transition quadratures have their exact printed values.
Use: gives the free-mass branch and the mass-bound transition without any numerical premise.
Article: jacobi, Theorem D.6.
Proof: integrate arcsin(v/sqrt(2)), v*sqrt(2-v²)/2, and
arcsin(v/sqrt(2))/2+v*(1-v²)*sqrt(2-v²)/4 on the actual closed interval. -/
theorem J_one_values : J 1 1=Real.pi/4 ∧ J 2 1=1/2 ∧ J 3 1=Real.pi/8 := by
  -- The polynomial square-root primitives are differentiated only inside the interval.
  let F (v : ℝ) := (1/2:ℝ)*v*sqrt (2-v^2)
  let G (v : ℝ) := (1/2:ℝ)*arcsin (v/sqrt 2)+(1/4:ℝ)*v*(1-v^2)*sqrt (2-v^2)
  have hp (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) : 0<2-v^2 := by
    nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  have hs (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) :
      HasDerivAt (fun x : ℝ => sqrt (2-x^2)) (-v/sqrt (2-v^2)) v := by
    convert (((hasDerivAt_id v).pow 2).const_sub 2).sqrt (hp v hv).ne' using 1
    · rfl
    · dsimp only [id_eq,Pi.pow_apply]
      norm_num
      ring
  have hF (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) : HasDerivAt F (weight 2 1 v) v := by
    rw [weight_one (by decide : 1≤2) hv]
    convert (((hasDerivAt_id v).mul (hs v hv)).const_mul (1/2:ℝ)) using 1
    · funext x; dsimp only [F,Pi.mul_apply,id_eq]; ring
    · dsimp only [id_eq]
      norm_num only [Nat.reduceSub,pow_one]
      field_simp [(sqrt_pos.mpr (hp v hv)).ne']
      nlinarith [sq_sqrt (hp v hv).le]
  have hG (v : ℝ) (hv : v∈Ioo (0:ℝ) 1) : HasDerivAt G (weight 3 1 v) v := by
    rw [weight_one (by decide : 1≤3) hv]
    convert ((angle_derivative hv).const_mul (1/2:ℝ)).add
      ((((hasDerivAt_id v).mul (((hasDerivAt_id v).pow 2).const_sub 1)).mul (hs v hv)).const_mul (1/4:ℝ)) using 1
    · funext x; dsimp only [G,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,id_eq]; ring
    · dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply]
      norm_num only [Nat.reduceSub,Nat.cast_ofNat,mul_one]
      field_simp [(sqrt_pos.mpr (hp v hv)).ne']
      nlinarith [sq_sqrt (hp v hv).le,
        congrArg (fun z : ℝ => v^2*z) (sq_sqrt (hp v hv).le)]
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    (f := fun v => arcsin (v/sqrt 2)) (f' := weight 1 1) (by fun_prop)
    (fun v hv => by simpa only [weight_one (by decide : 1≤1) hv,Nat.sub_self,pow_zero] using angle_derivative hv)
    (weight_integrable (by decide : 1≤1) (by norm_num))
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    (f := F) (by dsimp only [F]; fun_prop) hF (weight_integrable (by decide : 1≤2) (by norm_num))
  have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    (f := G) (by dsimp only [G]; fun_prop) hG (weight_integrable (by decide : 1≤3) (by norm_num))
  refine ⟨?_,?_,?_⟩
  · simpa only [J,angle_one,zero_div,arcsin_zero,sub_zero] using h1
  · norm_num [F] at h2
    exact h2
  · have ha : arcsin (sqrt (2:ℝ))⁻¹=Real.pi/4 := by simpa only [one_div] using angle_one
    norm_num [G,ha] at h3
    simpa only [J,show (1/2:ℝ)*(Real.pi/4)=Real.pi/8 by ring] using h3

/-- The limiting mass quadrature is exactly one third.
Use: fixes the lower endpoint of the mass equation's range and proves existence for every ell<M<3ell/2.
Article: jacobi, Theorem D.6.
Proof: v*sqrt(A(v))/3 is a true primitive of (1-v²)²/sqrt(A(v)); evaluate at zero and one. -/
theorem J_two_zero : J 2 0=1/3 := by
  -- The quartic A is strictly positive everywhere, so its square root has no interior singularity.
  have hA (v : ℝ) : 0<A v := by unfold A; nlinarith [sq_nonneg (v^2-(3/2:ℝ))]
  let F (v : ℝ) := (1/3:ℝ)*v*sqrt (A v)
  have hd (v : ℝ) (_hv : v∈Ioo (0:ℝ) 1) : HasDerivAt F (weight 2 0 v) v := by
    have hpoly : HasDerivAt A (-6*v+4*v^3) v := by
      convert ((((hasDerivAt_id v).pow 2).const_mul (-3)).add (((hasDerivAt_id v).pow 4))).add_const 3 using 1
      · funext x; dsimp only [A,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]; ring
      · dsimp only [id_eq]; norm_num; ring
    convert (((hasDerivAt_id v).mul (hpoly.sqrt (hA v).ne')).const_mul (1/3:ℝ)) using 1
    · funext x; dsimp only [F,Pi.mul_apply,id_eq]; ring
    · dsimp only [weight,P,id_eq]
      simp only [zero_mul,sub_zero,one_mul]
      field_simp [(sqrt_pos.mpr (hA v)).ne']
      have hh := sq_sqrt (hA v).le
      unfold A at hh ⊢
      nlinarith
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    (f := F) (by dsimp only [F,A]; fun_prop) hd (weight_integrable (by decide : 1≤2) (by norm_num))
  norm_num [F,A] at hh
  exact hh

end
end jacobi.Keller
