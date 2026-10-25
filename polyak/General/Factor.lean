import polyak.General.Parameters

/-! Article: eq:factor. Algebraic source identity at every nonzero complex point. -/
namespace polyak.General
noncomputable section
namespace Tuning

def m (q : Tuning) (z : ℂ) : ℂ := (z + (q.beta : ℂ)/z - q.A) / q.B

theorem one_sub_m (q : Tuning) {z : ℂ} (hz : z ≠ 0) :
    1-q.m z = -q.a z / ((q.B : ℂ)*z) := by
  have hB : (q.B : ℂ) ≠ 0 := by exact_mod_cast q.B_ne_zero
  have ha : (q.A : ℂ)+(q.B : ℂ)=(1+q.beta-q.x : ℝ) := by exact_mod_cast q.A_add_B
  dsimp [m,a]
  field_simp
  linear_combination z*ha

theorem one_add_m (q : Tuning) {z : ℂ} (hz : z ≠ 0) :
    1+q.m z = q.b z / ((q.B : ℂ)*z) := by
  have hB : (q.B : ℂ) ≠ 0 := by exact_mod_cast q.B_ne_zero
  have ha : (q.A : ℂ)-(q.B : ℂ)=(1+q.beta-q.y : ℝ) := by exact_mod_cast q.A_sub_B
  dsimp [m,b]
  field_simp
  linear_combination -z*ha

theorem factor (q : Tuning) {z : ℂ} (hz : z ≠ 0) :
    (1-q.m z)*(1+star (q.m z)) =
      -q.a z*star (q.b z) / ((q.B : ℂ)^2*(Complex.normSq z : ℂ)) := by
  rw [q.one_sub_m hz, show 1+star (q.m z)=star (1+q.m z) by simp,
    q.one_add_m hz]
  simp only [star_div₀, star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.mul_conj]
  ring

theorem real_im_factor (w : ℂ) :
    ((1-Complex.normSq w : ℝ) : ℂ)-2*Complex.I*(w.im : ℂ) = (1-w)*(1+star w) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

theorem m_wave (q : Tuning) (t ω : ℝ) :
    q.m (Waves.z t ω) = Waves.multiplier q.A q.B q.beta t ω := rfl

end Tuning
end
end polyak.General
