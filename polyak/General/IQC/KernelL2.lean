import polyak.General.IQC.CertificateSpace
import polyak.Energy.KernelEstimate

/-! Appendix D, lem:iqc and lem:homotopy: the finite Parseval inequality
extends to actual whole-line ℓ² signals by the canonical finite-support
approximations. This supplies the graph gap without assuming a Fourier
inequality as an external hypothesis. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def shiftBilinear (a b : ℤ) : ZSpace E →L[ℝ] ZSpace E →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (zShiftCLM a) (zShiftCLM b)

def kernelBilinear (K : Kernel) : ZSpace E →L[ℝ] ZSpace E →L[ℝ] ℝ :=
  (K.map fun p => p.1 • shiftBilinear p.2.1 p.2.2).sum

theorem kernelBilinear_apply (K : Kernel) (x y : ZSpace E) :
    kernelBilinear K x y=
      (K.map fun p => p.1*inner ℝ (zShift p.2.1 x) (zShift p.2.2 y)).sum := by
  induction K with
  | nil => simp [kernelBilinear]
  | cons p K ih =>
    change ((p.1 • shiftBilinear (E:=E) p.2.1 p.2.2 :
      ZSpace E →L[ℝ] ZSpace E →L[ℝ] ℝ)+kernelBilinear (E:=E) K) x y=_
    simp only [add_apply,smul_apply,smul_eq_mul,
      shiftBilinear,ContinuousLinearMap.bilinearComp_apply,innerSL_apply_apply,ih,List.map_cons,List.sum_cons]
    rfl

def zCutoff (S : Finset ℤ) (x : ZSpace E) : ZSpace E := ∑ k∈S,lp.single 2 k (x k)

theorem kernelEval_summable (K : Kernel) (x : ZSpace E) :
    Summable (fun k => kernelEval K x k) := by
  induction K with
  | nil => simp [kernelEval]
  | cons p K ih =>
    exact (Summable.mul_left p.1 (lp.summable_inner (zShift p.2.1 x) (zShift p.2.2 x))).add ih

theorem kernelBilinear_eq_tsum (K : Kernel) (x : ZSpace E) :
    kernelBilinear K x x=∑' k,kernelEval K x k := by
  induction K with
  | nil => simp [kernelBilinear,kernelEval]
  | cons p K ih =>
    have hs : Summable (fun k => p.1*inner ℝ (x (k+p.2.1)) (x (k+p.2.2))):=by
      simpa only [zShift_apply] using
        Summable.mul_left p.1 (lp.summable_inner (zShift p.2.1 x) (zShift p.2.2 x))
    change _=∑' k,(p.1*inner ℝ (x (k+p.2.1)) (x (k+p.2.2))+kernelEval K x k)
    rw [Summable.tsum_add hs (kernelEval_summable K x),←ih,tsum_mul_left]
    rw [kernelBilinear_apply,kernelBilinear_apply]
    rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem zCutoff_apply (S : Finset ℤ) (x : ZSpace E) (k : ℤ) :
    zCutoff S x k=if k∈S then x k else 0 := by
  classical
  simp only [zCutoff,lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Finset.sum_pi_single]

theorem inner_shift_zCutoff (S : Finset ℤ) (x : ZSpace E) (a b : ℤ) :
    inner ℝ (zShift a (zCutoff S x)) (zShift b (zCutoff S x))=
      finiteCorrelation S x (b-a) := by
  classical
  change (∑' k : ℤ,inner ℝ (zCutoff S x (k+a)) (zCutoff S x (k+b)))=_
  have ht : (∑' k : ℤ,inner ℝ (zCutoff S x (k+a)) (zCutoff S x (k+b)))=
      ∑' k : ℤ,inner ℝ (zCutoff S x k) (zCutoff S x (k+(b-a))):=by
    convert (Equiv.addRight a).tsum_eq
      (fun k => inner ℝ (zCutoff S x k) (zCutoff S x (k+(b-a)))) using 1
    congr 1
    funext k
    change inner ℝ (zCutoff S x (k+a)) (zCutoff S x (k+b))=
      inner ℝ (zCutoff S x (k+a)) (zCutoff S x (k+a+(b-a)))
    rw [show k+a+(b-a)=k+b by omega]
  rw [ht,finiteCorrelation_eq_single_sum]
  rw [tsum_eq_sum (s:=S) (fun k hk => by simp [hk])]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkb : k+(b-a)∈S <;> simp [hk,hkb]

theorem kernelBilinear_zCutoff (K : Kernel) (S : Finset ℤ) (x : ZSpace E) :
    kernelBilinear K (zCutoff S x) (zCutoff S x)=kernelCorrelation K S x := by
  rw [kernelBilinear_apply]
  unfold kernelCorrelation
  congr 1
  apply List.map_congr_left
  intro p _
  rw [inner_shift_zCutoff]

omit [InnerProductSpace ℝ E] in
theorem zCutoff_norm_sq (S : Finset ℤ) (x : ZSpace E) :
    ‖zCutoff S x‖^2=∑ k∈S,‖x k‖^2 := by
  simpa only [zCutoff,ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_sum_single (by norm_num : 0<(2 : ℝ≥0∞).toReal) (fun k => x k) S

theorem kernelBilinear_le (K : Kernel) {ε : ℝ}
    (hneg : ∀ θ,kernelSymbol K θ≤ -ε) (x : ZSpace E) :
    kernelBilinear K x x≤ -ε*‖x‖^2 := by
  have hlim : Filter.Tendsto (fun S : Finset ℤ => zCutoff S x) Filter.atTop (nhds x):=
    lp.hasSum_single (by norm_num : (2 : ℝ≥0∞)≠⊤) x
  have hleft : Continuous (fun y : ZSpace E => kernelBilinear K y y):=
    by fun_prop
  have hright : Continuous (fun y : ZSpace E => -ε*‖y‖^2):=by fun_prop
  apply le_of_tendsto_of_tendsto (hleft.tendsto x |>.comp hlim)
    (hright.tendsto x |>.comp hlim)
  exact Filter.Eventually.of_forall (fun S => by
    change kernelBilinear K (zCutoff S x) (zCutoff S x)≤ -ε*‖zCutoff S x‖^2
    rw [kernelBilinear_zCutoff,zCutoff_norm_sq]
    exact kernelCorrelation_le K S x hneg)

end polyak.General.IQC
