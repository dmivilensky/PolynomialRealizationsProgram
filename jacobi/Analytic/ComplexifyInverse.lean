import jacobi.Analytic.ContinuousMapHolomorphy
import Mathlib.Analysis.Normed.Operator.Banach

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
A complex-linear operator on continuous functions which extends an
invertible real operator is itself invertible. The proof constructs its
actual inverse images by the real and imaginary parts; no complex
solvability assumption is introduced.
Source: elementary complexification of an invertible real linear map.
Use: reduces the real base complex GL inverse to the already proved real inverse.
-/
namespace jacobi.Analytic
noncomputable section
open _root_.Complex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The actual real part of a continuous complex function.
Use: reduces the real base complex GL inverse to the already proved real inverse.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def continuousRealPart (f : C(X,ℂ)) : C(X,ℝ) :=
  ⟨fun x => (f x).re,Complex.continuous_re.comp f.continuous⟩

/-- The actual imaginary part of a continuous complex function.
Use: constructs the second real inverse image in the genuine complex base GL inverse.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def continuousImagPart (f : C(X,ℂ)) : C(X,ℝ) :=
  ⟨fun x => (f x).im,Complex.continuous_im.comp f.continuous⟩

/-- Inclusion of an original continuous real function into the complex continuous-function space.
Use: verifies that the complex GL operator at real order extends the same original real operator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def continuousOfReal (f : C(X,ℝ)) : C(X,ℂ) :=
  ⟨fun x => (f x:ℂ),Complex.continuous_ofReal.comp f.continuous⟩

omit [CompactSpace X] in
/-- A continuous complex function is exactly the complexification of its actual real and imaginary parts.
Use: proves invertibility of the original complex base GL operator from its genuine real inverse.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the two components and compare their complex coordinates. -/
theorem continuous_parts (f : C(X,ℂ)) :
    continuousOfReal (continuousRealPart f)+Complex.I • continuousOfReal (continuousImagPart f)=f := by
  ext x
  apply Complex.ext <;> simp [continuousOfReal,continuousRealPart,continuousImagPart,smul_eq_mul]

/-- A complex-linear continuous-function operator extending a genuine invertible real operator is itself genuinely invertible.
Use: supplies the actual complex GL inverse at the real base order before applying the local analytic inverse theorem.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: complexification of real linear isomorphisms and mathlib's Banach operator inverse theorem.
Proof: complex linearity and the real-extension identity split every image into the images of its real and imaginary parts. Real injectivity then gives complex injectivity. For any complex target take real inverse images of its two actual parts and combine them; this gives complex surjectivity. The Banach operator theorem provides a bounded complex inverse. -/
theorem isUnit_complex_of_real {A : C(X,ℂ) →L[ℂ] C(X,ℂ)}
    {B : C(X,ℝ) →L[ℝ] C(X,ℝ)} (hB : IsUnit B)
    (hcompat : ∀ f : C(X,ℝ),A (continuousOfReal f)=continuousOfReal (B f)) : IsUnit A := by
  -- Both inverse images are constructed by the same proved real inverse, applied to the actual target parts.
  obtain ⟨hinj,hsurj⟩ := ContinuousLinearMap.isUnit_iff_bijective.mp hB
  have hparts (f : C(X,ℂ)) : A f=
      continuousOfReal (B (continuousRealPart f))+Complex.I • continuousOfReal (B (continuousImagPart f)) := by
    calc
      _ = A (continuousOfReal (continuousRealPart f)+Complex.I • continuousOfReal (continuousImagPart f)) :=
        congrArg A (continuous_parts f).symm
      _ = _ := by rw [map_add,map_smul,hcompat,hcompat]
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · have hzero (f : C(X,ℂ)) (hf : A f=0) : f=0 := by
      have he := (hparts f).symm.trans hf
      have hr : B (continuousRealPart f)=0 := by
        ext x
        have hh := congrArg (fun g : C(X,ℂ) => (g x).re) he
        simpa [continuousOfReal,smul_eq_mul] using hh
      have hi : B (continuousImagPart f)=0 := by
        ext x
        have hh := congrArg (fun g : C(X,ℂ) => (g x).im) he
        simpa [continuousOfReal,smul_eq_mul] using hh
      have hfr : continuousRealPart f=0 := hinj (hr.trans B.map_zero.symm)
      have hfi : continuousImagPart f=0 := hinj (hi.trans B.map_zero.symm)
      ext x
      apply Complex.ext
      · exact congrArg (fun g : C(X,ℝ) => g x) hfr
      · exact congrArg (fun g : C(X,ℝ) => g x) hfi
    intro f g h
    exact sub_eq_zero.mp (hzero (f-g) (by rw [map_sub,h,sub_self]))
  · intro g
    obtain ⟨u,hu⟩ := hsurj (continuousRealPart g)
    obtain ⟨v,hv⟩ := hsurj (continuousImagPart g)
    refine ⟨continuousOfReal u+Complex.I • continuousOfReal v,?_⟩
    rw [map_add,map_smul,hcompat,hcompat,hu,hv,continuous_parts]

end
end jacobi.Analytic
