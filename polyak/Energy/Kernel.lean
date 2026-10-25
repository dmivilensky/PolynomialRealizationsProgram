import polyak.Energy.Certificate
import polyak.Energy.Fourier

/-!
Article: Appendix A, the finite translation-invariant quadratic form in Lemma energy.
Use: retain exact coefficients and integer shifts while eliminating the gradients.
Proof: finite linear filters and their real-Hilbert outer products.
-/

noncomputable section

namespace polyak.Energy

/-- Article: a finite real linear filter, coefficient first and integer shift second. -/
abbrev LinearFilter := List (ℝ × ℤ)

/-- Article: a finite real quadratic kernel, with two integer shifts in each term. -/
abbrev Kernel := List (ℝ × (ℤ × ℤ))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: application of a finite linear filter to a Hilbert sequence. -/
def filterEval (L : LinearFilter) (f : ℤ → E) (k : ℤ) : E :=
  (L.map fun p => p.1 • f (k+p.2)).sum

/-- Article: evaluation of a finite quadratic kernel. -/
def kernelEval (K : Kernel) (f : ℤ → E) (k : ℤ) : ℝ :=
  (K.map fun p => p.1 * inner ℝ (f (k+p.2.1)) (f (k+p.2.2))).sum

/-- Article: the full real frequency symbol of a finite quadratic kernel. -/
def kernelSymbol (K : Kernel) (θ : FrequencyCircle) : ℝ :=
  (K.map fun p => p.1 * (character (p.2.2-p.2.1) θ).re).sum

/-- Article: absolute coefficient mass, controlling every boundary quadratic term. -/
def kernelSize (K : Kernel) : ℝ := (K.map fun p => |p.1|).sum

/-- Article: multiply a filter by a real coefficient. -/
def filterScale (r : ℝ) (L : LinearFilter) : LinearFilter := L.map fun p => (r*p.1,p.2)

/-- Article: translate the filter by an integer lag. -/
def filterShift (n : ℤ) (L : LinearFilter) : LinearFilter := L.map fun p => (p.1,n+p.2)

/-- Article: multiply a quadratic kernel by a real coefficient. -/
def kernelScale (r : ℝ) (K : Kernel) : Kernel := K.map fun p => (r*p.1,p.2)

/-- Article: the outer product of two finite linear filters. -/
def filterOuter (L M : LinearFilter) : Kernel :=
  L.flatMap fun p => M.map fun q => (p.1*q.1,(p.2,q.2))

/-- Article: the position filter. -/
def unitFilter : LinearFilter := [(1,0)]

/-- Article: concatenating filters adds their actual values. -/
@[simp] theorem filterEval_append (L M : LinearFilter) (f : ℤ → E) (k : ℤ) :
    filterEval (L++M) f k = filterEval L f k + filterEval M f k := by
  simp [filterEval]

/-- Article: scaling a filter scales its actual value. -/
@[simp] theorem filterEval_scale (r : ℝ) (L : LinearFilter) (f : ℤ → E) (k : ℤ) :
    filterEval (filterScale r L) f k = r • filterEval L f k := by
  induction L with
  | nil => simp [filterScale, filterEval]
  | cons p L ih =>
    change (r*p.1) • f (k+p.2) + filterEval (filterScale r L) f k =
      r • (p.1 • f (k+p.2) + filterEval L f k)
    rw [ih, mul_smul, smul_add]

/-- Article: translating a filter translates its center index. -/
@[simp] theorem filterEval_shift (n : ℤ) (L : LinearFilter) (f : ℤ → E) (k : ℤ) :
    filterEval (filterShift n L) f k = filterEval L f (k+n) := by
  simp only [filterShift, filterEval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [add_assoc]

/-- Article: the unit filter evaluates to the sampled position. -/
@[simp] theorem filterEval_unit (f : ℤ → E) (k : ℤ) : filterEval unitFilter f k = f k := by
  simp [unitFilter, filterEval]

/-- Article: concatenating quadratic kernels adds their actual forms. -/
@[simp] theorem kernelEval_append (K L : Kernel) (f : ℤ → E) (k : ℤ) :
    kernelEval (K++L) f k = kernelEval K f k + kernelEval L f k := by
  simp [kernelEval]

/-- Article: scaling a kernel scales its actual form. -/
@[simp] theorem kernelEval_scale (r : ℝ) (K : Kernel) (f : ℤ → E) (k : ℤ) :
    kernelEval (kernelScale r K) f k = r * kernelEval K f k := by
  induction K with
  | nil => simp [kernelScale, kernelEval]
  | cons p K ih =>
    change (r*p.1) * inner ℝ (f (k+p.2.1)) (f (k+p.2.2)) +
      kernelEval (kernelScale r K) f k =
      r * (p.1 * inner ℝ (f (k+p.2.1)) (f (k+p.2.2)) + kernelEval K f k)
    rw [ih]
    ring

/-- Article: the filter outer product evaluates to the real Hilbert inner product.
Proof: finite bilinearity, with no completeness or dimension assumption. -/
@[simp] theorem kernelEval_outer (L M : LinearFilter) (f : ℤ → E) (k : ℤ) :
    kernelEval (filterOuter L M) f k = inner ℝ (filterEval L f k) (filterEval M f k) := by
  have hmap (p : ℝ × ℤ) (M : LinearFilter) :
      kernelEval (M.map fun q => (p.1*q.1,(p.2,q.2))) f k =
        inner ℝ (p.1 • f (k+p.2)) (filterEval M f k) := by
    induction M with
    | nil => simp [kernelEval, filterEval]
    | cons q M ih =>
      change (p.1*q.1) * inner ℝ (f (k+p.2)) (f (k+q.2)) +
        kernelEval (M.map fun q => (p.1*q.1,(p.2,q.2))) f k =
        inner ℝ (p.1 • f (k+p.2)) (q.1 • f (k+q.2) + filterEval M f k)
      rw [ih]
      simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right]
      ring
  induction L with
  | nil => simp [filterOuter, kernelEval, filterEval]
  | cons p L ih =>
    change kernelEval ((M.map fun q => (p.1*q.1,(p.2,q.2))) ++ filterOuter L M) f k =
      inner ℝ (p.1 • f (k+p.2) + filterEval L f k) (filterEval M f k)
    rw [kernelEval_append, hmap, ih, inner_add_left]

/-- Article: concatenating kernels adds their symbols. -/
@[simp] theorem kernelSymbol_append (K L : Kernel) (θ : FrequencyCircle) :
    kernelSymbol (K++L) θ = kernelSymbol K θ + kernelSymbol L θ := by
  simp [kernelSymbol]

/-- Article: scaling a kernel scales its symbol. -/
@[simp] theorem kernelSymbol_scale (r : ℝ) (K : Kernel) (θ : FrequencyCircle) :
    kernelSymbol (kernelScale r K) θ = r * kernelSymbol K θ := by
  induction K with
  | nil => simp [kernelScale, kernelSymbol]
  | cons p K ih =>
    change (r*p.1) * (character (p.2.2-p.2.1) θ).re +
      kernelSymbol (kernelScale r K) θ =
      r * (p.1 * (character (p.2.2-p.2.1) θ).re + kernelSymbol K θ)
    rw [ih]
    ring

/-- Article: all finite kernel symbols are continuous. -/
@[fun_prop] theorem continuous_kernelSymbol (K : Kernel) : Continuous (kernelSymbol K) := by
  induction K with
  | nil => change Continuous (fun _ : FrequencyCircle => (0 : ℝ)); exact continuous_const
  | cons p K ih =>
    change Continuous (fun θ => p.1 * (character (p.2.2-p.2.1) θ).re + kernelSymbol K θ)
    exact (continuous_const.mul (Complex.continuous_re.comp (character _).continuous)).add ih

/-- Article: evaluating a finite family of concatenated quadratic kernels. -/
theorem kernelEval_flatMap {I : Type*} (L : List I) (K : I → Kernel) (f : ℤ → E) (k : ℤ) :
    kernelEval (L.flatMap K) f k = (L.map fun i => kernelEval (K i) f k).sum := by
  induction L with
  | nil => rfl
  | cons i L ih => simpa only [List.flatMap_cons, kernelEval_append, List.map_cons,
      List.sum_cons] using congrArg (fun x => kernelEval (K i) f k + x) ih

/-- Article: the symbol of a finite family of concatenated quadratic kernels. -/
theorem kernelSymbol_flatMap {I : Type*} (L : List I) (K : I → Kernel) (θ : FrequencyCircle) :
    kernelSymbol (L.flatMap K) θ = (L.map fun i => kernelSymbol (K i) θ).sum := by
  induction L with
  | nil => rfl
  | cons i L ih => simpa only [List.flatMap_cons, kernelSymbol_append, List.map_cons,
      List.sum_cons] using congrArg (fun x => kernelSymbol (K i) θ + x) ih

/-- Article: a single Fourier character has exactly the required real Gram products. -/
theorem inner_character (i j : ℤ) (θ : FrequencyCircle) :
    inner ℝ (character i θ) (character j θ) = (character (j-i) θ).re := by
  rw [character_sub_re]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Article: the full quadratic symbol is evaluation on one unit complex Fourier wave.
Proof: every real-Hilbert coefficient has the same Gram product as the Fourier character. -/
theorem kernelSymbol_eq_eval (K : Kernel) (θ : FrequencyCircle) :
    kernelSymbol K θ = kernelEval K (fun k => character k θ) 0 := by
  unfold kernelSymbol kernelEval
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [zero_add]
  rw [inner_character]

/-- Article: real kernels have even symbols on the frequency circle. -/
theorem kernelSymbol_neg (K : Kernel) (θ : FrequencyCircle) :
    kernelSymbol K (-θ) = kernelSymbol K θ := by
  unfold kernelSymbol
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [character, fourier_apply, smul_neg, fourier_neg', Complex.conj_re]

end polyak.Energy
