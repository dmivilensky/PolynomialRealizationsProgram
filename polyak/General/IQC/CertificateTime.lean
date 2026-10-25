import polyak.Energy.Certificate
import polyak.General.IQC.SequenceSpace

/-! Article: lem:iqc(a), the absolutely convergent whole-line certificate.
All value terms cancel by translation invariance of the actual integer sum. -/
noncomputable section
namespace polyak.General.IQC
open polyak Interpolation Duality Spectral Energy

variable {E : Type*} [NormedAddCommGroup E]
variable {m : C(Frequency,ℂ)} {t : ℝ}

def ZSquareSummable (x : ℤ → E) : Prop := Summable (fun k => ‖x k‖^2)

theorem ZSquareSummable.shift {x : ℤ → E} (hx : ZSquareSummable x) (n : ℤ) :
    ZSquareSummable (fun k => x (k+n)) :=
  (Equiv.addRight n).summable_iff.2 hx

theorem ZSquareSummable.smul [NormedSpace ℝ E] {x : ℤ → E} (hx : ZSquareSummable x) (r : ℝ) :
    ZSquareSummable (fun k => r • x k) := by
  simpa only [ZSquareSummable,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using Summable.mul_left (r^2) hx

theorem ZSquareSummable.add {x y : ℤ → E} (hx : ZSquareSummable x)
    (hy : ZSquareSummable y) : ZSquareSummable (fun k => x k+y k) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    (Summable.mul_left 2 (Summable.add hx hy))
  intro k
  have hh := norm_add_le (x k) (y k)
  nlinarith [sq_nonneg (‖x k‖-‖y k‖),norm_nonneg (x k+y k),norm_nonneg (x k),norm_nonneg (y k)]

theorem ZSquareSummable.neg {x : ℤ → E} (hx : ZSquareSummable x) :
    ZSquareSummable (fun k => -x k) := by simpa only [ZSquareSummable,norm_neg] using hx
theorem ZSquareSummable.sub {x y : ℤ → E} (hx : ZSquareSummable x)
    (hy : ZSquareSummable y) : ZSquareSummable (fun k => x k-y k) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

variable [InnerProductSpace ℝ E]

theorem summable_Zinner {x y : ℤ → E} (hx : ZSquareSummable x)
    (hy : ZSquareSummable y) : Summable (fun k => inner ℝ (x k) (y k)) := by
  apply (Summable.div_const (Summable.add hx hy) 2).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs]
  exact abs_inner_le_half_sq (x k) (y k)

theorem summable_Zpair {x y σ τ : ℤ → E} (hx : ZSquareSummable x)
    (hy : ZSquareSummable y) (hσ : ZSquareSummable σ) (hτ : ZSquareSummable τ)
    (δ : ℝ) : Summable (fun k => pairQuadratic δ (x k) (y k) (σ k) (τ k)) := by
  exact Summable.sub (Summable.mul_left (1/4)
    (Summable.sub (ZSquareSummable.sub hy hx) (ZSquareSummable.sub hτ hσ)))
    (Summable.mul_left (δ/2) (summable_Zinner (ZSquareSummable.add hσ hτ) (ZSquareSummable.sub hy hx)))

theorem summable_Zstar {x σ : ℤ → E} (hx : ZSquareSummable x)
    (hσ : ZSquareSummable σ) (δ : ℝ) :
    Summable (fun k => starQuadratic δ (x k) (σ k)) :=
  Summable.sub (Summable.mul_left (1/4) (Summable.sub hx hσ))
    (Summable.mul_left (δ/2) (summable_Zinner hσ hx))

def zCertificateQuadratic (cert : StrictCertificate m t) (x σ : ℤ → E) (k : ℤ) : ℝ :=
  (∑ n ∈ cert.lags,2*Real.exp (-(n*t))*
    (cert.α n*pairQuadratic 1 (x k) (Real.exp (n*t) • x (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n))+
     cert.β n*pairQuadratic (-1) (x k) (Real.exp (n*t) • x (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n))))+
    4*cert.γplus*starQuadratic 1 (x k) (σ k)+
    4*cert.γminus*starQuadratic (-1) (x k) (σ k)

def zCertificateValue (cert : StrictCertificate m t) (v : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑ n ∈ cert.lags,2*Real.exp (n*t)*(cert.α n-cert.β n)*(v (k+n)-v k)

theorem summable_zCertificateQuadratic (cert : StrictCertificate m t)
    {x σ : ℤ → E} (hx : ZSquareSummable x) (hσ : ZSquareSummable σ) :
    Summable (zCertificateQuadratic cert x σ) := by
  apply Summable.add
  · apply Summable.add
    · apply summable_sum
      intro n _
      apply Summable.mul_left
      exact ((summable_Zpair hx ((hx.shift n).smul _) hσ ((hσ.shift n).smul _) 1).mul_left _).add
        ((summable_Zpair hx ((hx.shift n).smul _) hσ ((hσ.shift n).smul _) (-1)).mul_left _)
    · exact (summable_Zstar hx hσ 1).mul_left _
  · exact (summable_Zstar hx hσ (-1)).mul_left _

theorem summable_zCertificateValue (cert : StrictCertificate m t)
    {v : ℤ → ℝ} (hv : Summable v) : Summable (zCertificateValue cert v) := by
  apply summable_sum
  intro n _
  exact (((Equiv.addRight (n:ℤ)).summable_iff.2 hv).sub hv).mul_left _

theorem tsum_zCertificateValue (cert : StrictCertificate m t)
    {v : ℤ → ℝ} (hv : Summable v) : ∑' k,zCertificateValue cert v k=0 := by
  unfold zCertificateValue
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_eq_zero
    intro n _
    have hshift : Summable (fun k : ℤ => v (k+n)) := (Equiv.addRight (n:ℤ)).summable_iff.2 hv
    have he : (∑' k : ℤ,v (k+n))=∑' k : ℤ,v k := (Equiv.addRight (n:ℤ)).tsum_eq v
    rw [tsum_mul_left,hshift.tsum_sub hv,he,sub_self,mul_zero]
  · intro n _
    exact (((Equiv.addRight (n:ℤ)).summable_iff.2 hv).sub hv).mul_left _

theorem zCertificate_nonneg (cert : StrictCertificate m t) {x σ : ℤ → E}
    {v : ℤ → ℝ} (hx : ZSquareSummable x) (hσ : ZSquareSummable σ) (hv : Summable v)
    (hslack : ∀ k,0≤zCertificateQuadratic cert x σ k+zCertificateValue cert v k) :
    0≤∑' k,zCertificateQuadratic cert x σ k := by
  have hs : 0≤(∑' k,(zCertificateQuadratic cert x σ k+zCertificateValue cert v k)) := tsum_nonneg hslack
  rw [(summable_zCertificateQuadratic cert hx hσ).tsum_add
    (summable_zCertificateValue cert hv),tsum_zCertificateValue cert hv,add_zero] at hs
  exact hs

end polyak.General.IQC
