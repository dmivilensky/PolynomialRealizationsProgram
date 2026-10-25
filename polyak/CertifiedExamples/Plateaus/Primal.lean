import polyak.CertifiedExamples.Plateaus.Kernels
import polyak.ModeLocking.Regular.Definitions

/-! Transport the polynomial kernel to the actual spectral measure. The
positive phase factor is divided out before normalization; this is essential
for the original lag and minimizer constraints. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels
open scoped BigOperators

def phaseFactor (q : Tuning) (ω : Frequency) : ℝ :=
  Real.sin (q.angle ω)/Real.sin (ω : ℝ)

theorem phaseFactor_pos (q : Tuning) (ω : Frequency)
    (hω : 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) : 0<phaseFactor q ω :=
  div_pos (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2)
    (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)

def unnormalizedPrimal {d : ℕ} (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (i : Fin d) : ℝ := ρ i / phaseFactor q (u i)

def actualPrimal {d : ℕ} (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (i : Fin d) : ℝ :=
  unnormalizedPrimal q u ρ i / ∑ j,unnormalizedPrimal q u ρ j

theorem unnormalizedPrimal_pos {d : ℕ} (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (hu : ∀ i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi)
    (hρ : ∀ i,0<ρ i) (i : Fin d) : 0<unnormalizedPrimal q u ρ i :=
  div_pos (hρ i) (phaseFactor_pos q (u i) (hu i))

theorem primal_total_pos {d : ℕ} (hd : 0<d) (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (hu : ∀ i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi)
    (hρ : ∀ i,0<ρ i) : 0<∑ j,unnormalizedPrimal q u ρ j := by
  apply Finset.sum_pos
  · intro i _
    exact unnormalizedPrimal_pos q u ρ hu hρ i
  · exact ⟨⟨0,hd⟩,Finset.mem_univ _⟩

theorem actualPrimal_pos {d : ℕ} (hd : 0<d) (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (hu : ∀ i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi)
    (hρ : ∀ i,0<ρ i) (i : Fin d) : 0<actualPrimal q u ρ i :=
  div_pos (unnormalizedPrimal_pos q u ρ hu hρ i) (primal_total_pos hd q u ρ hu hρ)

theorem actualPrimal_sum {d : ℕ} (hd : 0<d) (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (hu : ∀ i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi)
    (hρ : ∀ i,0<ρ i) : (∑ i,actualPrimal q u ρ i)=1 := by
  unfold actualPrimal
  rw [← Finset.sum_div,div_self (primal_total_pos hd q u ρ hu hρ).ne']

theorem actualPrimal_lag {d : ℕ} (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (hu : ∀ i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi)
    (n : ℤ) (hn : n≠0) :
    (∑ i,actualPrimal q u ρ i*(tuningCurve q).lag n (u i)) =
      (∑ i,ρ i*Farey.Certificates.signedLagPolynomial q n (Real.cos (u i:ℝ)))/
        ∑ j,unnormalizedPrimal q u ρ j := by
  simp only [Farey.Certificates.lag_polynomial_factor q n hn _ (hu _)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hf := (phaseFactor_pos q (u i) (hu i)).ne'
  change (ρ i/phaseFactor q (u i)/(∑j,unnormalizedPrimal q u ρ j))*
    (phaseFactor q (u i)*Farey.Certificates.signedLagPolynomial q n (Real.cos (u i:ℝ)))=
      (ρ i*Farey.Certificates.signedLagPolynomial q n (Real.cos (u i:ℝ)))/_
  calc
    _ = ((ρ i/phaseFactor q (u i)*phaseFactor q (u i))*
        Farey.Certificates.signedLagPolynomial q n (Real.cos (u i:ℝ)))/(∑j,unnormalizedPrimal q u ρ j) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hf]

theorem actualPrimal_minimizer {d : ℕ} (q : Tuning) (u : Fin d → Frequency)
    (ρ : Fin d → ℝ) (hu : ∀ i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi) :
    (∑ i,actualPrimal q u ρ i*(tuningCurve q).minimizer (u i)) =
      (∑ i,ρ i*q.Xi (Real.cos (u i:ℝ)))/
        ∑ j,unnormalizedPrimal q u ρ j := by
  simp only [Farey.Certificates.minimizer_factor q _ (hu _)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hf := (phaseFactor_pos q (u i) (hu i)).ne'
  change (ρ i/phaseFactor q (u i)/(∑j,unnormalizedPrimal q u ρ j))*
    (phaseFactor q (u i)*q.Xi (Real.cos (u i:ℝ)))=(ρ i*q.Xi (Real.cos (u i:ℝ)))/_
  calc
    _ = ((ρ i/phaseFactor q (u i)*phaseFactor q (u i))*q.Xi (Real.cos (u i:ℝ)))/(∑j,unnormalizedPrimal q u ρ j) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hf]

end polyak.CertifiedExamples.Plateaus
