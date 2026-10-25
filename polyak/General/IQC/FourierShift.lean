import polyak.General.IQC.HomotopyFourier

/-! The actual Fourier transform of integer shifts. The proof starts with
single-coordinate basis signals, uses character multiplication pointwise,
and then passes to every whole-line l2 signal by its norm-convergent series.
-/
noncomputable section
namespace polyak.General.IQC.Fourier
open MeasureTheory
open scoped ENNReal
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

abbrev circleMeasure := AddCircle.haarAddCircle (T:=2*Real.pi)

def characterLp (n : ℤ) : Lp ℂ ∞ circleMeasure :=
  ContinuousMap.toLp ∞ circleMeasure ℂ (fourier (T:=2*Real.pi) n)

theorem characterLp_ae (n : ℤ) : characterLp n=ᵐ[circleMeasure] fourier (T:=2*Real.pi) n :=
  ContinuousMap.coeFn_toLp (p:=∞) (𝕜:=ℂ) circleMeasure _

/-- Bounded multiplication by the n-th Fourier character. -/
def mulCharacter (n : ℤ) : ScalarFrequency→L[ℝ]ScalarFrequency :=
  multiply (scalarOperator (characterLp n))

theorem mulCharacter_ae (n : ℤ) (f : ScalarFrequency) :
    mulCharacter n f=ᵐ[circleMeasure] fun ω=>fourier (T:=2*Real.pi) n ω*f ω := by
  filter_upwards [multiply_ae (scalarOperator (characterLp n)) f,
    scalarOperator_ae (characterLp n),characterLp_ae n] with ω hmul hscalar hchar
  change (multiply (scalarOperator (characterLp n)) f) ω=_
  rw [hmul,hscalar,hchar]

private theorem scalarUnitary_single (j : ℤ) (z : ℂ) :
    scalarUnitary (lp.single 2 j z)=z • fourierLp (T:=2*Real.pi) 2 j := by
  have he : lp.single (E:=fun _ : ℤ=>ℂ) 2 j z=z • lp.single 2 j (1:ℂ) := by
    simpa only [smul_eq_mul,mul_one] using lp.single_smul (E:=fun _ : ℤ=>ℂ) 2 j z (1:ℂ)
  change (fourierBasis (T:=2*Real.pi)).repr.symm (lp.single 2 j z)=_
  rw [he,map_smul,HilbertBasis.repr_symm_single]
  rw [coe_fourierBasis]

private theorem zShift_single (n j : ℤ) (z : ℂ) :
    polyak.General.IQC.zShift n (lp.single 2 j z)=lp.single 2 (j-n) z := by
  ext k
  have he : k+n=j ↔ k=j-n := by omega
  simp [polyak.General.IQC.zShift_apply,lp.single_apply,Pi.single_apply,he]

private theorem mulCharacter_single (n j : ℤ) (z : ℂ) :
    mulCharacter (-n) (scalarUnitary (lp.single 2 j z))=
      scalarUnitary (lp.single 2 (j-n) z) := by
  rw [scalarUnitary_single,scalarUnitary_single]
  apply Lp.ext
  filter_upwards [mulCharacter_ae (-n) (z • fourierLp (T:=2*Real.pi) 2 j),
    Lp.coeFn_smul z (fourierLp (T:=2*Real.pi) 2 j),
    Lp.coeFn_smul z (fourierLp (T:=2*Real.pi) 2 (j-n)),
    coeFn_fourierLp (T:=2*Real.pi) 2 j,coeFn_fourierLp (T:=2*Real.pi) 2 (j-n)]
    with ω hm hs hs' hj hj'
  rw [hm,hs,hs']
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hj,hj']
  rw [show j-n=(-n)+j by ring,fourier_add]
  ring

/-- Actual shift/Fourier identity for every l2 signal, with the source sign. -/
theorem scalarUnitary_shift (n : ℤ) (x : ScalarTime) :
    scalarUnitary (polyak.General.IQC.zShift n x)=mulCharacter (-n) (scalarUnitary x) := by
  have hx := lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x
  have hl := ((scalarUnitary.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (polyak.General.IQC.zShiftCLM (E:=ℂ) n)).hasSum hx
  have hr := ((mulCharacter (-n)).comp scalarUnitary.toContinuousLinearEquiv.toContinuousLinearMap).hasSum hx
  have he (j : ℤ) : scalarUnitary (polyak.General.IQC.zShift n (lp.single 2 j (x j)))=
      mulCharacter (-n) (scalarUnitary (lp.single 2 j (x j))) := by
    rw [zShift_single,mulCharacter_single]
  change HasSum (fun j : ℤ=>scalarUnitary (polyak.General.IQC.zShift n (lp.single 2 j (x j)))) _ at hl
  change HasSum (fun j : ℤ=>mulCharacter (-n) (scalarUnitary (lp.single 2 j (x j)))) _ at hr
  simp only [he] at hl
  exact hl.unique hr

end polyak.General.IQC.Fourier
