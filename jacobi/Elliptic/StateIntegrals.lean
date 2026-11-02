import jacobi.Elliptic.ProfileQuadrature

/-!
Article: jacobi, Theorem D.5.
All quadratures here are actual finite integrals of the normalized optimizer
state. The original density, energy and spectral second moment equal their
printed amplitude factors times I_2, I_3 and J. The equalities use the
proved global state substitution and actual Green potential normalization.
Source: the article's elliptic quadrature calculation, with its Jacobian proved.
Use: gives the printed I_k before rescaling the turning height to one.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The literal turning-height power quadrature of the normalized elliptic state.
Use: gives the printed I_k before rescaling the turning height to one.
Article: jacobi, Theorem D.5.
-/
def stateIntegral (σ Y : ℝ) (k : ℕ) : ℝ :=
  ∫ v in Ioo (0:ℝ) Y,v^k/sqrt ((v-σ)^2-v^3)

/-- The literal mixed turning-height quadrature for the second spectral moment.
Use: its amplitude factor gives G_2 of the actual optimizer.
Article: jacobi, Theorem D.5.
-/
def stateMixedIntegral (σ Y : ℝ) : ℝ :=
  ∫ v in Ioo (0:ℝ) Y,v^2*(v-σ)/sqrt ((v-σ)^2-v^3)

/-- Positive integer powers of the actual optimizer state equal their genuine turning-height quadratures.
Use: supplies I_2 and I_3 for the original mass and energy integrals.
Article: jacobi, Theorem D.5.
Proof: specialize the proved whole-line observable substitution and remove
the positive-part clipping on the strictly positive target interval. -/
theorem eulerState_power_integral (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l)
    (k : ℕ) (hk : 0<k) :
    (∫ x,(max (eulerState m μ l x) 0)^k)=
      stateIntegral (eulerShift μ l) (eulerState m μ l 0) k := by
  -- The observable vanishes throughout the nonpositive tail, not just almost everywhere.
  rw [eulerState_quadrature m hm hs hμ hl he (fun v => (max v 0)^k)
    (fun v hv => by rw [max_eq_right hv,zero_pow (by omega)]),stateIntegral]
  exact setIntegral_congr_fun measurableSet_Ioo fun v hv => by rw [max_eq_left hv.1.le]

/-- The actual normalized Green potential has the exact amplitude stated in the elliptic calibration.
Use: evaluates the original density-potential pairing as the J quadrature.
Article: jacobi, Theorem D.5.
Proof: substitute a=27/(16mu), the actual state and its shift, and cancel the positive multiplier. -/
theorem potential_eulerState (m : Density) {μ : ℝ} (hμ : 0<μ) (l x : ℝ) :
    potential m x=(8/27:ℝ)*(eulerScale μ)^2*(eulerState m μ l x-eulerShift μ l) := by
  unfold eulerState eulerShift eulerScale
  field_simp
  ring

/-- The original actual optimizer mass and energy equal their exact I_2 and I_3 quadratures.
Use: eliminates the Euler amplitude in the exact elliptic infimum formula.
Article: jacobi, Theorem D.5.
Proof: the actual density and its energy integrand equal their normalized
positive-part powers a.e. Pull out the constant factors and apply the
proved whole-line power substitution to that same actual optimizer. -/
theorem euler_mass_energy_quadratures (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    m.mass=(4/9:ℝ)*(eulerScale μ)^2*stateIntegral (eulerShift μ l) (eulerState m μ l 0) 2 ∧
      m.energy=(8/27:ℝ)*(eulerScale μ)^3*stateIntegral (eulerShift μ l) (eulerState m μ l 0) 3 := by
  -- The original measurable density is retained; only a.e. equal integrands are substituted.
  have hmass : m.mass=∫ x,eulerDensity m μ l x := integral_congr_ae he
  have henergy : m.energy=∫ x,(eulerDensity m μ l x)^(3/2:ℝ) :=
    integral_congr_ae (he.fun_comp (fun v : ℝ => v^(3/2:ℝ)))
  constructor
  · rw [hmass]
    simp_rw [eulerDensity_normalized m hμ]
    rw [integral_const_mul,eulerState_power_integral m hm hs hμ hl he 2 (by decide)]
  · rw [henergy]
    simp_rw [eulerDensity_energy m hμ]
    rw [integral_const_mul,eulerState_power_integral m hm hs hμ hl he 3 (by decide)]

/-- The actual optimizer's spectral second moment equals the exact mixed J quadrature.
Use: identifies the attained moment ratio with the printed elliptic parameter equation.
Article: jacobi, Theorem D.5.
Proof: the actual spectral moment is its Green density-potential pairing.
Substitute the proved original Euler density and exact potential scaling,
then apply the actual positive-core substitution to v_+²*(v-sigma). -/
theorem euler_second_quadrature (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    observe m .second=(32/243:ℝ)*(eulerScale μ)^4*
      stateMixedIntegral (eulerShift μ l) (eulerState m μ l 0) := by
  -- The quadrature evaluates the same actual G_2 which defines the variational constraint.
  have hG : observe m .second=∫ x,m.value x*potential m x := by
    rw [← m.secondPairing_self,secondPairing_iterated m.integrable m.integrable m.measurable m.measurable]
    simp_rw [potential_kernel]
  rw [hG]
  have hi : (∫ x,m.value x*potential m x)=
      (32/243:ℝ)*(eulerScale μ)^4*
        (∫ x,(max (eulerState m μ l x) 0)^2*(eulerState m μ l x-eulerShift μ l)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx,eulerDensity_normalized m hμ,potential_eulerState m hμ]
    ring
  rw [hi,eulerState_quadrature m hm hs hμ hl he
    (fun v => (max v 0)^2*(v-eulerShift μ l))
    (fun v hv => by rw [max_eq_right hv,zero_pow (by decide : 2≠0),zero_mul]),stateMixedIntegral]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioo fun v hv => by rw [max_eq_left hv.1.le]

end
end jacobi.Elliptic
