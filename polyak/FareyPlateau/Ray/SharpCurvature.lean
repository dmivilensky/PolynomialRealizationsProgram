import polyak.FareyPlateau.Ray.SharpMoment

/-! The sharp source inequality Rλ(c₀)≥a₂, retaining its exact equality
condition: the support must be the adjacent two lags. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set

theorem SourceCertificate.curvature_moment_identity {j k : ℕ} {b : ℤ} {D a t : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    4*(Real.sin (Real.pi/k))^3*Real.sin (Regions.rationalAngle j k)*
      oneMass k b C.lag C.weight*
        (C.R (Chart.rationalCosine j k)-edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t)=
    Real.cos (Real.pi/k)*(curvatureMoment C.lag C.weight
      (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)-
        oneMass k b C.lag C.weight*(k:ℝ)^2*t*(1-t)) := by
  have h1 := C.second_contact hj hjk hb q he
  have h2 := C.second_moment hj hjk hb q he
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : Real.pi/k∈Ioo (0:ℝ) Real.pi :=
    ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hk⟩
  have h3 := edge_curvature_a2 (k:=(k:ℝ)) (t:=t) q hω hγ he (source_edge_phase q hj hjk he)
  linear_combination h2-h1-2*oneMass k b C.lag C.weight*h3

theorem cos_phase_pos {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k) : 0<Real.cos (Real.pi/k) := by
  have hk : (3:ℝ)≤k := by exact_mod_cast (show 3≤k by omega)
  have hp : 0<Real.pi/(k:ℝ) := div_pos Real.pi_pos (by linarith)
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨by linarith [Real.pi_pos],?_⟩
  apply (div_lt_iff₀ (by linarith : (0:ℝ)<k)).mpr
  nlinarith [Real.pi_pos]

theorem SourceCertificate.sharp_curvature {j k : ℕ} {b n₁ : ℤ} {D a t : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t≤C.R (Chart.rationalCosine j k) := by
  have hid := C.curvature_moment_identity (t:=t) hj hjk hb q he
  have hmoment := C.sharp_moment (by omega) hb ht0 ht1 hn₁ hbar
  have hpos := cos_phase_pos hj hjk
  have hnonneg := mul_nonneg hpos.le (sub_nonneg.mpr hmoment)
  rw [←hid] at hnonneg
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hsγ := Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith : (0:ℝ)<k))
    (div_lt_self Real.pi_pos hk)
  have hsω := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hμ := oneMass_pos C.admissible
  have hp : 0<4*(Real.sin (Real.pi/k))^3*Real.sin (Regions.rationalAngle j k)*
      oneMass k b C.lag C.weight := by positivity
  have hh := (mul_nonneg_iff_of_pos_left hp).mp hnonneg
  linarith

theorem SourceCertificate.sharp_curvature_eq_iff {j k : ℕ} {b n₁ : ℤ} {D a t : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    C.R (Chart.rationalCosine j k)=edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t ↔
      ∀i,C.lag i=n₁ ∨ C.lag i=n₁+k := by
  have hid := C.curvature_moment_identity (t:=t) hj hjk hb q he
  have hmoment := C.sharp_moment_eq_iff (by omega) hb ht0 ht1 hn₁ hbar
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hsγ := Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith : (0:ℝ)<k))
    (div_lt_self Real.pi_pos hk)
  have hsω := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hμ := oneMass_pos C.admissible
  have hp : 0<4*(Real.sin (Real.pi/k))^3*Real.sin (Regions.rationalAngle j k)*
      oneMass k b C.lag C.weight := by positivity
  have hcos := cos_phase_pos hj hjk
  constructor
  · intro heq
    rw [heq,sub_self,mul_zero] at hid
    have heq' := (mul_eq_zero.mp hid.symm).resolve_left hcos.ne'
    exact hmoment.mp (sub_eq_zero.mp heq')
  · intro heq
    rw [hmoment.mpr heq,sub_self,mul_zero] at hid
    have heq' := (mul_eq_zero.mp hid).resolve_left hp.ne'
    exact sub_eq_zero.mp heq'

end polyak.FareyPlateau.Ray
