import krylov.Tensor.BinaryFibre

/-!
Article: main_krylov, thm:Fplanar, regularity of the genuine fibre minimax.
Use: transport actual admissible cubic chords between nearby observations.
Source: a direct coefficient estimate and the exact linear shear of binary
cubics. The numerical continuity constant here is deliberately nonsharp;
the minimax value and the sharp value 1/3 remain the actual ones.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section

/-- Elementary coordinate bounds in the actual diagonal-norm ball.
Article: main_krylov, thm:Fplanar, local boundedness used in the shear argument.
Proof: test (1,1) and (1,-1), using homogeneity at radius sqrt2, and the axes.
This estimate does not assume Banach's diagonal-to-mixed norm identity. -/
theorem mixed_coefficients_le_two {t : BinaryCubic} (ht : t.InBall) :
    |t.t1|≤2 ∧ |t.t2|≤2 := by
  have hr : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hr3 : (Real.sqrt 2)^3≤3 := by
    have he : (Real.sqrt 2)^3=2*Real.sqrt 2 := by nlinarith
    nlinarith [Real.sqrt_nonneg 2]
  have hp := (bound_at_radius ht 1 1 (Real.sqrt 2) hr (by norm_num [hr2])).trans hr3
  have hq := (bound_at_radius ht 1 (-1) (Real.sqrt 2) hr (by norm_num [hr2])).trans hr3
  obtain ⟨h0,h3⟩ := axis_bounds ht
  obtain ⟨hp0,hp1⟩ := abs_le.mp hp
  obtain ⟨hq0,hq1⟩ := abs_le.mp hq
  obtain ⟨h00,h01⟩ := abs_le.mp h0
  obtain ⟨h30,h31⟩ := abs_le.mp h3
  simp only [eval] at hp0 hp1 hq0 hq1
  constructor <;> apply abs_le.mpr <;> constructor <;> norm_num at * <;> linarith

/-- A uniform genuine upper bound on every chord objective.
Article: main_krylov, thm:Fplanar, local boundedness of M_F. -/
theorem chordValue_le {r : ℝ} {y z : BinaryCubic} (h : Chord r y z) :
    chordValue r y z≤4*(1+|r|) := by
  obtain ⟨hy,hz,_⟩ := h
  obtain ⟨hy1,hy2⟩ := mixed_coefficients_le_two hy
  obtain ⟨_,hz2⟩ := mixed_coefficients_le_two hz
  have hP : |y.t1+r*y.t2|≤2+2*|r| := by
    calc
      |y.t1+r*y.t2| ≤ |y.t1|+|r| *|y.t2| := by simpa [abs_mul] using abs_add_le y.t1 (r*y.t2)
      _ ≤ 2+|r| *2 := add_le_add hy1 (mul_le_mul_of_nonneg_left hy2 (abs_nonneg r))
      _ = 2+2*|r| := by ring
  have hD : |y.t2-z.t2|≤4 := by
    exact (abs_sub y.t2 z.t2).trans (by linarith)
  unfold chordValue
  have hm := mul_le_mul hP hD (abs_nonneg _) (by positivity : 0≤2+2*|r|)
  nlinarith

/-- The actual value set is bounded above, with a common bound on compact r sets.
Article: main_krylov, thm:Fplanar. -/
theorem chordValues_bddAbove (r : ℝ) : BddAbove (chordValues r) := by
  refine ⟨4*(1+|r|),?_⟩
  rintro v ⟨y,z,h,rfl⟩
  exact chordValue_le h

/-- The true coefficient is nonnegative and obeys a concrete local upper bound.
Article: main_krylov, thm:Fplanar. -/
theorem fibreMinimax_bounds (r : ℝ) : 0≤fibreMinimax r ∧ fibreMinimax r≤4*(1+|r|) := by
  constructor
  · exact le_csSup (chordValues_bddAbove r) (zero_mem_chordValues r)
  · apply csSup_le ⟨0,zero_mem_chordValues r⟩
    rintro v ⟨y,z,h,rfl⟩
    exact chordValue_le h

/-- The exact linear shear and uniform scaling used to transport real chords.
Article: main_krylov, thm:Fplanar, L_(r,r') followed by normalization. -/
def shearScale (r r' : ℝ) (t : BinaryCubic) : BinaryCubic :=
  let q := (1+6*|r-r'|)⁻¹
  ⟨q*t.t0,q*(t.t1+(r-r')*t.t2),q*t.t2,q*t.t3⟩

/-- Every scaled shear endpoint really lies in the cubic ball.
Article: main_krylov, thm:Fplanar.
Proof: the added cubic is 3(r-r')t2*c²*s. The true elementary coefficient
bound controls it by 6|r-r'| on the circle, exactly the chosen normalization. -/
theorem shearScale_inBall {t : BinaryCubic} (ht : t.InBall) (r r' : ℝ) :
    (shearScale r r' t).InBall := by
  intro c s hcs
  have hden : 0<1+6*|r-r'| := by positivity
  have hc2 : c^2≤1 := by nlinarith [sq_nonneg s]
  have hs : |s|≤1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg c]
  have ht2 := (mixed_coefficients_le_two ht).2
  have hadd : |3*(r-r')*t.t2*c^2*s|≤6*|r-r'| := by
    rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg c)]
    norm_num
    calc
      3*|r-r'| *|t.t2| *c^2*|s| ≤ 3*|r-r'| *2*1*1 := by
        gcongr
      _ = 6*|r-r'| := by ring
  have he : (shearScale r r' t).eval c s=
      (1+6*|r-r'|)⁻¹*(t.eval c s+3*(r-r')*t.t2*c^2*s) := by
    simp only [shearScale,eval]
    ring
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hden)]
  have hb := (abs_add_le (t.eval c s) (3*(r-r')*t.t2*c^2*s)).trans (add_le_add (ht c s hcs) hadd)
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hden.le)).trans_eq (inv_mul_cancel₀ hden.ne')

/-- Actual observation chords are carried to actual observation chords.
Article: main_krylov, thm:Fplanar, the shear preserves the measured P1. -/
theorem shearScale_chord {r r' : ℝ} {y z : BinaryCubic} (h : Chord r y z) :
    Chord r' (shearScale r r' y) (shearScale r r' z) := by
  obtain ⟨hy,hz,h0,h3,hP⟩ := h
  refine ⟨shearScale_inBall hy r r',shearScale_inBall hz r r',?_,?_,?_⟩
  · simp only [shearScale,h0]
  · simp only [shearScale,h3]
  · dsimp only [shearScale]
    linear_combination (1+6*|r-r'|)⁻¹*hP

/-- The true chord objective scales exactly quadratically under the transport.
Article: main_krylov, thm:Fplanar, the two-sided comparison of M_F. -/
theorem shearScale_chordValue (r r' : ℝ) (y z : BinaryCubic) :
    chordValue r' (shearScale r r' y) (shearScale r r' z)=
      (1+6*|r-r'|)⁻¹^2*chordValue r y z := by
  have hq : 0≤(1+6*|r-r'|)⁻¹ := by positivity
  have hP : (shearScale r r' y).t1+r'*(shearScale r r' y).t2=
      (1+6*|r-r'|)⁻¹*(y.t1+r*y.t2) := by dsimp only [shearScale];ring
  have hD : (shearScale r r' y).t2-(shearScale r r' z).t2=
      (1+6*|r-r'|)⁻¹*(y.t2-z.t2) := by dsimp only [shearScale];ring
  simp only [chordValue,hP,hD,abs_mul,abs_of_nonneg hq]
  ring

/-- A true quantitative comparison between the full minimax coefficients.
Article: main_krylov, thm:Fplanar, proof of local Lipschitz regularity.
Proof: transport every actual chord, then take its real supremum; no
assumption about a maximizing chord or a preselected fibre is needed. -/
theorem fibreMinimax_shear (r r' : ℝ) :
    fibreMinimax r≤(1+6*|r-r'|)^2*fibreMinimax r' := by
  have hden : 0<1+6*|r-r'| := by positivity
  apply csSup_le ⟨0,zero_mem_chordValues r⟩
  rintro v ⟨y,z,h,rfl⟩
  have hm : chordValue r' (shearScale r r' y) (shearScale r r' z)≤fibreMinimax r' :=
    le_csSup (chordValues_bddAbove r') ⟨_,_,shearScale_chord h,rfl⟩
  rw [shearScale_chordValue] at hm
  have hp := mul_le_mul_of_nonneg_left hm (sq_nonneg (1+6*|r-r'|))
  have he : (1+6*|r-r'|)^2*((1+6*|r-r'|)⁻¹^2*chordValue r y z)=chordValue r y z := by
    field_simp
  rwa [he] at hp

end
end krylov.Tensor.BinaryCubic
