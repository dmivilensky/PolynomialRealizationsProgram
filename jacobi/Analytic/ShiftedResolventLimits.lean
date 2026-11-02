import jacobi.Analytic.ShiftedMatrixIdentity
import jacobi.Analytic.ShiftedEnergyLimits
import jacobi.Analysis.ScaledSquareSum

/-!
Article: jacobi, Corollary C.6.
The original actual shifted complex matrix inverses satisfy all three
printed right-edge limits on every compact slit-domain set: the full
physical bound, exact floor profiles, and both distinct N-cubed energies.
All finite poles are excluded internally by the genuine spectral theory.
Use: all three direct shifted-resolvent conclusions below replace the proved spectral sums by the actual original matrix inverse uniformly.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Comparison
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- On every original compact admissible shift set, the actual finite
complex matrix inverse is eventually the same genuine spectral diagonal.
Use: all three direct shifted-resolvent conclusions below replace the
proved spectral sums by the actual original matrix inverse uniformly.
Article: jacobi, Corollary C.6.
Proof: the true compact finite denominator bound excludes every mode
at once; the independently proved exact finite matrix identity applies. -/
theorem shiftedTargetResolvent_identification {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ᶠn:ℕ in atTop,∀w∈W,∀i:Fin (n+1),
      finiteShiftedDiagonal a b ha hb n i w=
        shiftedTargetResolvent a b ha hb n w i i/(((n:ℝ)+1:ℝ):ℂ) := by
  obtain ⟨_,_,hden⟩ := finite_denominator_compact ha hb hW hsub
  filter_upwards [hden] with n hn w hw i
  exact finiteShiftedDiagonal_matrix a b ha hb n i w (fun k => (hn k w hw).1)

/-- The actual original shifted resolvent diagonal has the complete
uniform physical bound on every genuine compact admissible shift set.
Use: this is Theorem C.5, and provides the common actual bound in
both shifted-energy limits without an extra finite pole assumption.
Article: jacobi, Corollary C.6.
Proof: the actual finite complex inverse equals the proved genuine
spectral diagonal uniformly after one common dimension threshold;
its true physical normalization has a positive real denominator. -/
theorem shiftedTargetResolvent_bound {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),∀w∈W,
      ‖shiftedTargetResolvent a b ha hb n w i i‖/((n:ℝ)+1)≤C := by
  obtain ⟨C,hC,hbound⟩ := finiteShiftedDiagonal_bound ha hb hW hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,shiftedTargetResolvent_identification ha hb hW hsub] with n hn hid i w hw
  have hh := hn i w hw
  rw [hid w hw i,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ)<(n:ℝ)+1)] at hh
  exact hh

/-- The actual original complex matrix diagonal has the printed exact
floor-row shifted-profile limit uniformly over every compact shift set.
Use: this is all of the right-edge physical convergence in Theorem C.5,
with the original edge point, original candidate and original floor row.
Article: jacobi, Corollary C.6.
Proof: the genuine exact floor-row spectral limit is already uniform;
the same actual matrix identity holds after a common compact threshold. -/
theorem shiftedTargetResolvent_floor_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha)
    (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      ‖shiftedTargetResolvent a b ha hb n w (floorMatrixIndex n t ht) (floorMatrixIndex n t ht)/
        (((n:ℝ)+1:ℝ):ℂ)-shiftedProfile a ha ⟨t,⟨ht.1.le,ht.2.le⟩⟩ w‖<ε := by
  obtain ⟨NI,hNI⟩ := eventually_atTop.mp (shiftedTargetResolvent_identification ha hb hW hsub)
  intro ε hε
  obtain ⟨NP,hNP⟩ := finiteShiftedDiagonal_floor_uniform ha hb hW hsub t ht ε hε
  refine ⟨max NI NP,fun n hn w hw => ?_⟩
  rw [← hNI n (by omega) w hw (floorMatrixIndex n t ht)]
  exact hNP n (by omega) w hw

/-- The genuine actual complex-square matrix-resolvent energy has its
full printed N-cubed limit uniformly over every original compact shift set.
Use: this is the first energy assertion of Theorem C.5, for the actual
matrix inverse rather than a formal spectral or polynomial surrogate.
Article: jacobi, Corollary C.6.
Proof: replace the proved original spectral diagonal by the actual
finite complex matrix inverse at every physical row. The exact original
scalar square-sum identity gives precisely the printed N-cubed energy. -/
theorem shiftedTargetSquare_energy_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      ‖(∑i:Fin (n+1),(shiftedTargetResolvent a b ha hb n w i i)^2)/((((n:ℝ)+1:ℝ):ℂ)^3)-
        (∫t:Interval,(shiftedProfile a ha t w)^2)‖<ε := by
  obtain ⟨NI,hNI⟩ := eventually_atTop.mp (shiftedTargetResolvent_identification ha hb hW hsub)
  intro ε hε
  obtain ⟨NE,hNE⟩ := finiteShiftedSquare_energy_uniform ha hb hW hsub ε hε
  refine ⟨max NI NE,fun n hn w hw => ?_⟩
  have hh := hNE n (by omega) w hw
  simp_rw [hNI n (by omega) w hw] at hh
  rw [scaled_complex_square_sum] at hh
  exact hh

/-- The genuine actual modulus-square matrix-resolvent energy has its
full printed N-cubed limit uniformly over every original compact shift set.
Use: this is the second, distinct energy assertion of Theorem C.5,
retaining the actual complex modulus in every finite and limiting term.
Article: jacobi, Corollary C.6.
Proof: the same actual finite matrix identity replaces every original
spectral diagonal. The exact positive-real normalization for squared
moduli gives the original printed N-cubed finite energy. -/
theorem shiftedTargetNormSquare_energy_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      |(∑i:Fin (n+1),‖shiftedTargetResolvent a b ha hb n w i i‖^2)/((n:ℝ)+1)^3-
        (∫t:Interval,‖shiftedProfile a ha t w‖^2)|<ε := by
  obtain ⟨NI,hNI⟩ := eventually_atTop.mp (shiftedTargetResolvent_identification ha hb hW hsub)
  intro ε hε
  obtain ⟨NE,hNE⟩ := finiteShiftedNormSquare_energy_uniform ha hb hW hsub ε hε
  refine ⟨max NI NE,fun n hn w hw => ?_⟩
  have hh := hNE n (by omega) w hw
  simp_rw [hNI n (by omega) w hw] at hh
  rw [scaled_norm_square_sum] at hh
  exact hh

end
end jacobi.EdgeResolvent
