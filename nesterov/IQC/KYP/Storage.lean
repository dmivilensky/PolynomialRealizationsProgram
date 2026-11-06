import nesterov.IQC.KYP.ShiftRegister

/-!
A proved finite-state KYP lemma for the finite forward kernels used here.
Its quadratic storage is the attained infinite-horizon value of the actual
shift register. This proves existence from the strict Fourier gap, without
assuming a matrix inequality or invoking an external KYP theorem.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped InnerProductSpace
open polyak.General.IQC polyak.Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual half-line cost on a finite initial head and an ℓ² future. -/
def costForm (N : ℕ) (K : NatKernel) : Bilinear ((Fin N→E)×SequenceSpace E):=
  (halfKernel K).bilinearComp (spliceCLM N) (spliceCLM N)

@[simp] theorem costForm_apply (N : ℕ) (K : NatKernel) (x y : Fin N→E) (u v : SequenceSpace E) :
    costForm N K (x,u) (y,v)=halfKernel K (spliceCLM N (x,u)) (spliceCLM N (y,v)):=rfl

theorem costForm_symmetric (N : ℕ) (K : NatKernel)
    (a b : (Fin N→E)×SequenceSpace E) : costForm N K a b=costForm N K b a:=
  halfKernel_symmetric K _ _

theorem splice_zero_head (N : ℕ) (u : SequenceSpace E) :
    spliceCLM N (0,u)=delayCLM N u := by
  apply Subtype.ext
  funext k
  simp only [spliceCLM_apply,Pi.zero_apply,delayCLM_apply]
  by_cases hk : k<N <;> simp [hk,show N≤k ↔ ¬k<N by omega]

/-- The strict Fourier gap gives coercivity of the actual cost input block. -/
theorem costForm_coercive {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    {ε : ℝ} (hε : 0<ε) (hgap : ∀ θ,kernelSymbol K.toKernel θ≤ -ε) :
    IsCoercive (inputForm (costForm (E:=E) N K)) := by
  refine ⟨ε,hε,fun u=>?_⟩
  have hg:=halfKernel_delay_gap hK hgap u
  change ε*‖u‖*‖u‖≤ -halfKernel K (spliceCLM N (0,u)) (spliceCLM N (0,u))
  rw [splice_zero_head]
  nlinarith

variable [CompleteSpace E]

/-- A genuine bounded quadratic storage on the fixed N-dimensional state. -/
def storageForm {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    {ε : ℝ} (hε : 0<ε) (hgap : ∀ θ,kernelSymbol K.toKernel θ≤ -ε) : Bilinear (Fin N→E):=
  valueForm (costForm N K) (costForm_coercive hK hε hgap)

theorem storageForm_symmetric {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    {ε : ℝ} (hε : 0<ε) (hgap : ∀ θ,kernelSymbol K.toKernel θ≤ -ε) (x y : Fin N→E) :
    storageForm hK hε hgap x y=storageForm hK hε hgap y x :=
  costForm_symmetric N K _ _

/-- Finite-state KYP dissipation, proved by the actual optimal future and the
exact splice identity. No controllability or storage hypothesis is assumed. -/
theorem storageForm_dissipation {N : ℕ} (hN : 0<N) {K : NatKernel} (hK : K.Supported N)
    {ε : ℝ} (hε : 0<ε) (hgap : ∀ θ,kernelSymbol K.toKernel θ≤ -ε)
    (x : Fin N→E) (d : E) :
    instantaneous K x d+storageForm hK hε hgap (registerStep x d) (registerStep x d)≤
      storageForm hK hε hgap x x := by
  let Q:=costForm (E:=E) N K
  have hc:=costForm_coercive (E:=E) hK hε hgap
  let next:=registerStep x d
  let v:=optimizer Q hc next
  let u:=prependL2 d v
  have hb:=le_value Q (costForm_symmetric N K) hc x u
  change halfKernel K (spliceCLM N (x,u)) (spliceCLM N (x,u))≤_ at hb
  rw [splice_cost_split hN hK] at hb
  have hzero : u 0=d:=prependL2_zero d v
  have htail : advanceCLM 1 u=v:=advance_prepend d v
  rw [hzero,htail] at hb
  exact hb

end
end nesterov.IQC.KYP
