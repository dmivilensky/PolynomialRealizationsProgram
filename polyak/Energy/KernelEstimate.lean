import polyak.Energy.Kernel
import polyak.Energy.Localization

/-!
Article: Appendix A, finite Parseval and quadratic boundary estimate in Lemma energy.
Use: the complete finite kernel, with an explicit coefficient boundary constant.
Proof: scalar Fourier orthogonality for finite Hilbert Gram polynomials, then
finite-set cutoff localization term by term.
-/

noncomputable section

open MeasureTheory

namespace polyak.Energy

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: the complete quadratic form on a finitely supported Hilbert sequence. -/
def kernelCorrelation (K : Kernel) (S : Finset ℤ) (f : ℤ → E) : ℝ :=
  (K.map fun p => p.1 * finiteCorrelation S f (p.2.2-p.2.1)).sum

/-- Article: exact Parseval identity for a finite kernel and a finite Hilbert sequence. -/
theorem integral_kernelSymbol_mul_fourierGram (K : Kernel) (S : Finset ℤ) (f : ℤ → E) :
    (∫ θ : FrequencyCircle, kernelSymbol K θ *
      fourierGram (fun k : S => (k : ℤ)) (fun k : S => f k) θ
        ∂AddCircle.haarAddCircle) = kernelCorrelation K S f := by
  classical
  induction K with
  | nil => simp [kernelSymbol, kernelCorrelation]
  | cons p K ih =>
    have hcont : Continuous (fun θ : FrequencyCircle =>
        p.1 * (character (p.2.2-p.2.1) θ).re *
          fourierGram (fun k : S => (k : ℤ)) (fun k : S => f k) θ) :=
      (continuous_const.mul (Complex.continuous_re.comp (character _).continuous)).mul
        (continuous_fourierGram _ _)
    have hcont' : Continuous (fun θ : FrequencyCircle =>
        kernelSymbol K θ * fourierGram (fun k : S => (k : ℤ)) (fun k : S => f k) θ) :=
      (continuous_kernelSymbol K).mul (continuous_fourierGram _ _)
    change (∫ θ : FrequencyCircle,
      (p.1 * (character (p.2.2-p.2.1) θ).re + kernelSymbol K θ) *
        fourierGram (fun k : S => (k : ℤ)) (fun k : S => f k) θ
          ∂AddCircle.haarAddCircle) =
      p.1 * finiteCorrelation S f (p.2.2-p.2.1) + kernelCorrelation K S f
    simp_rw [add_mul]
    rw [integral_add (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hcont'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      ih]
    congr 1
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_character_mul_fourierGram, integerCorrelation_subtype]

/-- Article: the full quadratic form is strictly negative by the exact strict symbol gap. -/
theorem kernelCorrelation_le (K : Kernel) (S : Finset ℤ) (f : ℤ → E)
    {ε : ℝ} (hneg : ∀ θ, kernelSymbol K θ ≤ -ε) :
    kernelCorrelation K S f ≤ -ε * ∑ k ∈ S, ‖f k‖^2 := by
  classical
  rw [← integral_kernelSymbol_mul_fourierGram]
  have h := integral_symbol_mul_fourierGram_le
    (fun k : S => (k : ℤ)) (fun _ _ he => Subtype.ext he) (fun k : S => f k)
    (continuous_kernelSymbol K) hneg
  rwa [Finset.sum_coe_sort S (fun k => ‖f k‖^2)] at h

/-- Article: quadratic coefficient mass is nonnegative. -/
theorem kernelSize_nonneg (K : Kernel) : 0 ≤ kernelSize K := by
  unfold kernelSize
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg p.1)

/-- Article: the complete kernel cutoff discrepancy is bounded by its coefficient mass.
Proof: sum the proved single-term discrepancy, retaining all coefficient signs. -/
theorem abs_sum_kernelEval_sub_correlation_le (K : Kernel) (S T B : Finset ℤ)
    (f : ℤ → E) (hST : S ⊆ T)
    (hcover : ∀ p ∈ K, ∀ l ∈ S, l-p.2.1 ∈ T)
    (hboundary : ∀ p ∈ K, ∀ k ∈ T,
      ¬ (k ∈ S ↔ k+p.2.1 ∈ S ∧ k+p.2.2 ∈ S) →
        k+p.2.1 ∈ B ∧ k+p.2.2 ∈ B) :
    |(∑ k ∈ S, kernelEval K f k) - kernelCorrelation K S f| ≤
      kernelSize K * ∑ l ∈ B, ‖f l‖^2 := by
  classical
  induction K with
  | nil => simp [kernelEval, kernelCorrelation, kernelSize]
  | cons p K ih =>
    have hp := abs_local_sum_sub_finiteCorrelation_le S T B f p.2.1 p.2.2 hST
      (hcover p List.mem_cons_self) (hboundary p List.mem_cons_self)
    have hi := ih (fun q hq => hcover q (List.mem_cons_of_mem _ hq))
      (fun q hq => hboundary q (List.mem_cons_of_mem _ hq))
    have hsum : (∑ k ∈ S, kernelEval (p::K) f k) =
        p.1 * (∑ k ∈ S, inner ℝ (f (k+p.2.1)) (f (k+p.2.2))) +
          ∑ k ∈ S, kernelEval K f k := by
      change (∑ k ∈ S, (p.1 * inner ℝ (f (k+p.2.1)) (f (k+p.2.2)) +
        kernelEval K f k)) = _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum]
    change |p.1 * (∑ k ∈ S, inner ℝ (f (k+p.2.1)) (f (k+p.2.2))) +
        (∑ k ∈ S, kernelEval K f k) -
          (p.1 * finiteCorrelation S f (p.2.2-p.2.1) + kernelCorrelation K S f)| ≤
      (|p.1| + kernelSize K) * ∑ l ∈ B, ‖f l‖^2
    calc
      _ = |p.1 * ((∑ k ∈ S, inner ℝ (f (k+p.2.1)) (f (k+p.2.2))) -
            finiteCorrelation S f (p.2.2-p.2.1)) +
          ((∑ k ∈ S, kernelEval K f k) - kernelCorrelation K S f)| := by congr 1; ring
      _ ≤ |p.1 * ((∑ k ∈ S, inner ℝ (f (k+p.2.1)) (f (k+p.2.2))) -
            finiteCorrelation S f (p.2.2-p.2.1))| +
          |(∑ k ∈ S, kernelEval K f k) - kernelCorrelation K S f| := abs_add_le _ _
      _ ≤ |p.1| * (∑ l ∈ B, ‖f l‖^2) +
          kernelSize K * ∑ l ∈ B, ‖f l‖^2 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) hi
      _ = _ := by ring

/-- Article: quadratic localization estimate, with an exact finite-kernel symbol hypothesis.
Use: the certificate-specific symbol identity discharges that hypothesis separately. -/
theorem sum_kernelEval_le_of_symbol (K : Kernel) (S T B : Finset ℤ) (f : ℤ → E)
    {ε : ℝ} (hneg : ∀ θ, kernelSymbol K θ ≤ -ε) (hST : S ⊆ T)
    (hcover : ∀ p ∈ K, ∀ l ∈ S, l-p.2.1 ∈ T)
    (hboundary : ∀ p ∈ K, ∀ k ∈ T,
      ¬ (k ∈ S ↔ k+p.2.1 ∈ S ∧ k+p.2.2 ∈ S) →
        k+p.2.1 ∈ B ∧ k+p.2.2 ∈ B) :
    (∑ k ∈ S, kernelEval K f k) ≤
      -ε * (∑ k ∈ S, ‖f k‖^2) + kernelSize K * ∑ l ∈ B, ‖f l‖^2 := by
  have hquad := kernelCorrelation_le K S f hneg
  have hbound := abs_sum_kernelEval_sub_correlation_le K S T B f hST hcover hboundary
  linarith [le_abs_self ((∑ k ∈ S, kernelEval K f k) - kernelCorrelation K S f)]

end polyak.Energy
