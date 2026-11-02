import krylov.Tensor.BinarySharp

/-!
Article: main_krylov, apD:lem-binary(c) and thm:Fplanar.
Use: define the actual remaining-coefficient chord problem and prove its
sharp value at zero, with genuine admissible endpoints.
Source: reflection and convexity in the diagonal cubic ball; the exact
1/3 certificate is reused from BinarySharp.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section

/-- The hidden product bound also holds in absolute value, by reflection.
Article: main_krylov, apD:lem-binary(b,c). -/
theorem zero_slice_abs_product_le {t : BinaryCubic} (ht : t.InBall) (h0 : t.t0=0) :
    |t.t1*t.t2|≤1/3 := by
  apply abs_le.mpr
  constructor
  · have h := zero_slice_product_le (inBall_reflect_first ht) (by simp [h0])
    dsimp only at h
    nlinarith
  · exact zero_slice_product_le ht h0

/-- A true information chord fixes the two pure coefficients and the measured
mixed coefficient P1=t1+r*t2. Article: main_krylov, thm:Fplanar. -/
def Chord (r : ℝ) (y z : BinaryCubic) : Prop :=
  y.InBall ∧ z.InBall ∧ y.t0=z.t0 ∧ y.t3=z.t3 ∧ y.t1+r*y.t2=z.t1+r*z.t2

/-- Half of the actual chord length times the magnitude of its observation.
Article: main_krylov, thm:Fplanar, the pairwise definition of M_F. -/
def chordValue (r : ℝ) (y z : BinaryCubic) : ℝ :=
  |y.t1+r*y.t2| *|y.t2-z.t2|/2

/-- The exact set of all true binary-cubic fibre objective values.
Article: main_krylov, thm:Fplanar. -/
def chordValues (r : ℝ) : Set ℝ :=
  {v | ∃ y z : BinaryCubic, Chord r y z ∧ v=chordValue r y z}

/-- The actual function-value information coefficient, with all admissible
chords quantified rather than chosen in advance.
Article: main_krylov, thm:Fplanar, M_F(r). -/
def fibreMinimax (r : ℝ) : ℝ := sSup (chordValues r)

/-- Chord objective values are nonnegative, including degenerate chords.
Article: main_krylov, thm:Fplanar. -/
theorem chordValue_nonneg (r : ℝ) (y z : BinaryCubic) : 0≤chordValue r y z := by
  unfold chordValue
  positivity

/-- The cubic ball contains its genuine zero polynomial.
Article: main_krylov, thm:Fplanar, nonempty chord domain. -/
theorem zero_inBall : (⟨0,0,0,0⟩ : BinaryCubic).InBall := by
  intro c s _
  norm_num [eval]

/-- The true chord domain always includes its zero chord.
Article: main_krylov, thm:Fplanar. -/
theorem zero_mem_chordValues (r : ℝ) : 0∈chordValues r := by
  refine ⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,?_,?_⟩
  · exact ⟨zero_inBall,zero_inBall,rfl,rfl,rfl⟩
  · norm_num [chordValue]

/-- Reflecting and averaging the endpoints of a zero-shear chord produces
an actual admissible zero-slice cubic with the same hidden half-width.
Article: main_krylov, apD:lem-binary(c).
Proof: average y(c,s) and z(-c,s); the fixed pure coefficient cancels. -/
theorem chord_zero_symmetrization {y z : BinaryCubic} (h : Chord 0 y z) :
    (⟨0,y.t1,(y.t2-z.t2)/2,y.t3⟩ : BinaryCubic).InBall := by
  obtain ⟨hy,hz,h0,h3,h1⟩ := h
  have h1' : y.t1=z.t1 := by simpa using h1
  intro c s hcs
  have hp := hy c s hcs
  have hq := hz (-c) s (by nlinarith)
  have he : (⟨0,y.t1,(y.t2-z.t2)/2,y.t3⟩ : BinaryCubic).eval c s=
      (y.eval c s+z.eval (-c) s)/2 := by
    simp only [eval,← h0,← h1',← h3]
    ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hb := (abs_add_le (y.eval c s) (z.eval (-c) s)).trans (add_le_add hp hq)
  linarith

/-- Every true zero-shear chord has objective at most the printed sharp value.
Article: main_krylov, apD:lem-binary(c). -/
theorem chordValue_zero_le {y z : BinaryCubic} (h : Chord 0 y z) :
    chordValue 0 y z≤1/3 := by
  have hb := zero_slice_abs_product_le (chord_zero_symmetrization h) rfl
  dsimp only at hb
  simpa [chordValue,abs_mul,abs_div,mul_div_assoc] using hb

/-- The printed sharp cubic and its reflection are genuinely indistinguishable
under the zero-shear observations and span a sharp chord.
Article: main_krylov, apD:lem-binary(c). -/
theorem sharp_chord_zero :
    Chord 0 sharpCubic (⟨0,sharpCubic.t1,-sharpCubic.t2,sharpCubic.t3⟩ : BinaryCubic) := by
  refine ⟨sharpCubic_inBall,?_,rfl,rfl,?_⟩
  · simpa [sharpCubic] using inBall_reflect_first sharpCubic_inBall
  · simp

/-- The exact sharp chord has objective 1/3 in the true information problem.
Article: main_krylov, apD:lem-binary(c). -/
theorem sharp_chord_zero_value :
    chordValue 0 sharpCubic (⟨0,sharpCubic.t1,-sharpCubic.t2,sharpCubic.t3⟩ : BinaryCubic)=1/3 := by
  have hpos : 0<1/Real.sqrt 3 := by positivity
  have he : chordValue 0 sharpCubic
      (⟨0,sharpCubic.t1,-sharpCubic.t2,sharpCubic.t3⟩ : BinaryCubic)=
      sharpCubic.t1*sharpCubic.t2 := by
    dsimp only [chordValue,sharpCubic]
    rw [zero_mul,add_zero,sub_neg_eq_add,abs_of_pos hpos,
      abs_of_pos (by positivity : 0<1/Real.sqrt 3+1/Real.sqrt 3)]
    ring
  exact he.trans sharpCubic_product

/-- The genuine binary cubic fibre minimax coefficient at zero is exactly 1/3.
Article: main_krylov, apD:lem-binary(c), M_F(0)=1/3.
Proof: all admissible chords obey the proved upper bound, and the printed
extremizer and its reflection give actual endpoints attaining it. -/
theorem fibreMinimax_zero : fibreMinimax 0=1/3 := by
  have hupper : ∀ v∈chordValues 0, v≤(1/3 : ℝ) := by
    rintro v ⟨y,z,h,rfl⟩
    exact chordValue_zero_le h
  have hsharp : (1/3 : ℝ)∈chordValues 0 :=
    ⟨sharpCubic,⟨0,sharpCubic.t1,-sharpCubic.t2,sharpCubic.t3⟩,
      sharp_chord_zero,sharp_chord_zero_value.symm⟩
  exact le_antisymm (csSup_le ⟨0,zero_mem_chordValues 0⟩ hupper)
    (le_csSup ⟨1/3,hupper⟩ hsharp)

end
end krylov.Tensor.BinaryCubic
