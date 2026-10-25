import polyak.Energy.Symbol

/-!
Article: Appendix C, uniform bounds for the actual finite kernel coefficients.
Use: exact absolute coefficient masses of real filters and their outer products;
these bounds are independent of the number of square factors subsequently used.
-/
noncomputable section
namespace polyak.Energy

def filterSize (L : LinearFilter) : ℝ:=(L.map fun p => |p.1|).sum

theorem filterSize_nonneg (L : LinearFilter) : 0≤filterSize L := by
  unfold filterSize
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p,_,rfl⟩:=List.mem_map.mp hx
  exact abs_nonneg _

@[simp] theorem filterSize_append (L M : LinearFilter) : filterSize (L++M)=filterSize L+filterSize M:=by
  simp [filterSize]

@[simp] theorem filterSize_scale (r : ℝ) (L : LinearFilter) : filterSize (filterScale r L)=|r| *filterSize L:=by
  induction L with
  | nil => simp [filterSize,filterScale]
  | cons p L ih =>
    change |r*p.1|+filterSize (filterScale r L)=|r| *(|p.1|+filterSize L)
    rw [abs_mul,ih]
    ring

@[simp] theorem filterSize_shift (n : ℤ) (L : LinearFilter) : filterSize (filterShift n L)=filterSize L:=by
  simp [filterSize,filterShift,List.map_map,Function.comp_def]

@[simp] theorem filterSize_unit : filterSize unitFilter=1:=by simp [filterSize,unitFilter]

@[simp] theorem kernelSize_append (K L : Kernel) : kernelSize (K++L)=kernelSize K+kernelSize L:=by
  simp [kernelSize]

@[simp] theorem kernelSize_scale (r : ℝ) (K : Kernel) : kernelSize (kernelScale r K)=|r| *kernelSize K:=by
  induction K with
  | nil => simp [kernelSize,kernelScale]
  | cons p K ih =>
    change |r*p.1|+kernelSize (kernelScale r K)=|r| *(|p.1|+kernelSize K)
    rw [abs_mul,ih]
    ring

@[simp] theorem kernelSize_outer (L M : LinearFilter) : kernelSize (filterOuter L M)=filterSize L*filterSize M:=by
  have hm (p : ℝ×ℤ) : kernelSize (M.map fun q => (p.1*q.1,(p.2,q.2)))=|p.1| *filterSize M:=by
    induction M with
    | nil => simp [kernelSize,filterSize]
    | cons q M ih =>
      change |p.1*q.1|+kernelSize (M.map fun q => (p.1*q.1,(p.2,q.2)))=|p.1| *(|q.1|+filterSize M)
      rw [abs_mul,ih]
      ring
  induction L with
  | nil => simp [filterOuter,kernelSize,filterSize]
  | cons p L ih =>
    change kernelSize ((M.map fun q => (p.1*q.1,(p.2,q.2)))++filterOuter L M)=_
    rw [kernelSize_append,hm,ih]
    change |p.1| *filterSize M+filterSize L*filterSize M=(|p.1|+filterSize L)*filterSize M
    ring

theorem kernelSize_flatMap {I : Type*} (L : List I) (K : I → Kernel) :
    kernelSize (L.flatMap K)=(L.map fun i => kernelSize (K i)).sum:=by
  induction L with
  | nil => rfl
  | cons i L ih =>
    simpa only [List.flatMap_cons,kernelSize_append,List.map_cons,List.sum_cons] using
      congrArg (fun x => kernelSize (K i)+x) ih

theorem pairKernel_size (δ : ℝ) (hδ : |δ|=1) (X Y S T : LinearFilter) :
    kernelSize (pairKernel δ X Y S T)=(1/4 : ℝ)*(filterSize X+filterSize Y+filterSize S+filterSize T)^2:=by
  simp only [pairKernel,kernelSize_append,kernelSize_scale,kernelSize_outer,
    filterDifference,filterSize_append,filterSize_scale,abs_neg,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤4),abs_one,hδ,
    abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  ring

theorem starKernel_size (δ : ℝ) (hδ : |δ|=1) (X S : LinearFilter) :
    kernelSize (starKernel δ X S)=(1/4 : ℝ)*(filterSize X+filterSize S)^2:=by
  simp only [starKernel,kernelSize_append,kernelSize_scale,kernelSize_outer,
    abs_neg,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤4),abs_one,hδ,
    abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  ring

theorem lagKernel_size (A B β t : ℝ) (n : ℕ) (δ : ℝ) (hδ : |δ|=1) :
    kernelSize (lagKernel A B β t n δ)=
      (1/4 : ℝ)*(1+Real.exp (n*t))^2*(1+filterSize (gradientFilter A B β t))^2:=by
  rw [lagKernel,pairKernel_size δ hδ]
  simp only [filterSize_unit,filterSize_scale,filterSize_shift,abs_of_pos (Real.exp_pos _)]
  ring

end polyak.Energy
