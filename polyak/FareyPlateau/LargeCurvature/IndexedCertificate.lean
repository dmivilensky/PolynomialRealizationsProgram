import polyak.FareyPlateau.Edge.Certificate

/-! A finite indexed symbol is translated to the literal signed-lag
certificate without changing its function or any moment. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels ModeLocking
open scoped BigOperators
variable {I : Type*} [Fintype I]

def supportLags (n : I → ℤ) : Finset ℤ := Finset.univ.image n
def supportWeight (n : I → ℤ) (w : I → ℝ) (l : ℤ) : ℝ := ∑ i, if n i = l then w i else 0
def indexedSymbol (q : Tuning) (s : ℝ) (n : I → ℤ) (w : I → ℝ) (x : ℝ) : ℝ :=
  ∑ i, w i * lagExtension q s (n i) x

theorem supportWeight_at {n : I → ℤ} (hn : Function.Injective n) (w : I → ℝ) (i : I) :
    supportWeight n w (n i) = w i := by
  classical
  simp only [supportWeight, hn.eq_iff]
  simp

theorem sum_support {n : I → ℤ} (hn : Function.Injective n) (w : I → ℝ) (f : ℤ → ℝ) :
    (∑ l ∈ supportLags n, supportWeight n w l * f l) = ∑ i, w i * f (n i) := by
  classical
  rw [supportLags, Finset.sum_image (fun i _ j _ h => hn h)]
  simp only [supportWeight_at hn]

theorem indexedSymbol_eq {n : I → ℤ} (hn : Function.Injective n)
    (w : I → ℝ) (q : Tuning) (s : ℝ) :
    finiteSymbol q s (supportLags n) (supportWeight n w) = indexedSymbol q s n w := by
  funext x
  exact sum_support hn w (fun l => lagExtension q s l x)

def indexedCertificate {q : Tuning} {s : ℝ} {j k : ℕ}
    (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : 2 * j < k)
    (b : ℤ) (hb0 : 0 < b) (hbk : b < k) (hb : b * (j : ℤ) ≡ 1 [ZMOD (k : ℤ)])
    (n : I → ℤ) (w : I → ℝ) (hn : Function.Injective n)
    (hn0 : ∀ i, n i ≠ 0) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hclass : ∀ i, n i % (k : ℤ) = 0 ∨ n i % (k : ℤ) = b)
    (hpair : ∃ i l, n i ≠ n l ∧ n i % (k : ℤ) = b ∧ n l % (k : ℤ) = b)
    (hphase : Geometry.shiftedCurve q s (Edge.atom j k (by omega) hjk.le) = Real.pi / k)
    (hstrict : ∀ x : ℝ, 0 < x → x ≤ Real.pi →
      x ≠ (Edge.atom j k (by omega) hjk.le : ℝ) → indexedSymbol q s n w x < 0)
    (hcurv : deriv^[2] (indexedSymbol q s n w) (Edge.atom j k (by omega) hjk.le : ℝ) < 0)
    (hend : 0 < ∑ i, w i * (n i : ℝ) * ((n i : ℝ) + 2 * Geometry.tau q)) :
    Edge.Certificate q s j k where
  period_ge := hk
  numerator_pos := hj
  numerator_lt := hjk
  inverse := b
  inverse_pos := hb0
  inverse_lt := hbk
  inverse_mod := hb
  phase := hphase
  lags := supportLags n
  nonzero := by
    intro l hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
    exact hn0 i
  classes := by
    intro l hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
    exact hclass i
  weight := supportWeight n w
  weight_pos := by
    intro l hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
    rw [supportWeight_at hn]
    exact hw i
  weight_sum := by
    have hh := sum_support hn w (fun _ => 1)
    simpa only [mul_one, hsum] using hh
  pair := by
    obtain ⟨i, l, hne, hi, hl⟩ := hpair
    exact ⟨n i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
      n l, Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩, hne, hi, hl⟩
  strict := by
    rw [indexedSymbol_eq hn]
    exact hstrict
  curvature := by
    rw [indexedSymbol_eq hn]
    exact hcurv
  endpoint := by
    have hh : (∑ l ∈ supportLags n, supportWeight n w l * (l : ℝ) * ((l : ℝ) + 2 * Geometry.tau q)) =
        ∑ i, w i * (n i : ℝ) * ((n i : ℝ) + 2 * Geometry.tau q) := by
      simp only [mul_assoc]
      exact sum_support hn w (fun l => (l : ℝ) * ((l : ℝ) + 2 * Geometry.tau q))
    rwa [hh]

end polyak.FareyPlateau.LargeCurvature
