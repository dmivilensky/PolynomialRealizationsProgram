import polyak.FareyPlateau.Ray.SharpResults

/-! The adjacent lags and the function a₂(D) are defined directly from
the source slope by integer floor. Nonresonance alone supplies every
adjacency hypothesis in the sharp comparison. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels

def lowerLag (k : ℕ) (b : ℤ) (bar : ℝ) : ℤ := b+⌊(bar-b)/k⌋*(k:ℤ)
def edgeFraction (k : ℕ) (b : ℤ) (bar : ℝ) : ℝ := (bar-lowerLag k b bar)/k

theorem lowerLag_class (k : ℕ) (b : ℤ) (bar : ℝ) : lowerLag k b bar%k=b%k := by
  exact Int.add_mul_emod_self_right _ _ _

theorem floor_adjacent {k : ℕ} (hk : 0<k) (b : ℤ) (bar : ℝ)
    (hres : ∀m : ℤ,bar≠(b:ℝ)+m*k) :
    0<edgeFraction k b bar ∧ edgeFraction k b bar<1 ∧
      bar=(lowerLag k b bar:ℝ)+edgeFraction k b bar*k := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  let m : ℤ := ⌊(bar-b)/k⌋
  have hn : (lowerLag k b bar:ℝ)=(b:ℝ)+m*k := by
    simp only [lowerLag,m,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  have hlo : (lowerLag k b bar:ℝ)≤bar := by
    have hh := (le_div_iff₀ hkR).mp (Int.floor_le ((bar-b)/k))
    rw [hn]
    linarith
  have hhi : bar<(lowerLag k b bar:ℝ)+k := by
    have hh := (div_lt_iff₀ hkR).mp (Int.lt_floor_add_one ((bar-b)/k))
    rw [hn]
    linarith
  have hlt : (lowerLag k b bar:ℝ)<bar :=
    lt_of_le_of_ne hlo (by rw [hn];exact Ne.symm (hres m))
  refine ⟨div_pos (sub_pos.mpr hlt) hkR,(div_lt_one hkR).mpr (by linarith),?_⟩
  dsimp only [edgeFraction]
  rw [div_mul_cancel₀ _ hkR.ne']
  ring

def a2 (j k : ℕ) (b : ℤ) (D : ℝ) : ℝ :=
  edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D
    (edgeFraction k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D))

def edgeSymbol {j k : ℕ} {b : ℤ} {D : ℝ} (hk : 0<k) (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    SourceCertificate j k b D :=
  adjacentCertificate hk hb (lowerLag_class k b _)
    (floor_adjacent hk b _ hres).1 (floor_adjacent hk b _ hres).2.1
    (floor_adjacent hk b _ hres).2.2

theorem edgeSymbol_contact {K j k : ℕ} {b : ℤ} {D : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    (edgeSymbol hf.1 hb hres).R (Chart.rationalCosine j k)=a2 j k b D :=
  adjacent_contact_value hK hf hb (floor_adjacent hf.1 b _ hres).1
    (floor_adjacent hf.1 b _ hres).2.1 (lowerLag_class k b _)
    (floor_adjacent hf.1 b _ hres).2.2

theorem a2_le_aF_nonresonant {K j k : ℕ} {b : ℤ} {D : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    a2 j k b D≤aF j k b D :=
  a2_le_aF hK hf hb (floor_adjacent hf.1 b _ hres).1
    (floor_adjacent hf.1 b _ hres).2.1 (lowerLag_class k b _)
    (floor_adjacent hf.1 b _ hres).2.2

theorem aF_le_edgeSymbol_maximum {K j k : ℕ} {b : ℤ} {D : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    aF j k b D≤(edgeSymbol hf.1 hb hres).maximum := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  exact aF_le_maximum _ (by omega) hjk hb

end polyak.FareyPlateau.Ray
