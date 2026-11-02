import jacobi.Analytic.UniformShiftedProfiles
import jacobi.Analysis.CompactFullMeshIntegral
import jacobi.Analysis.SquareError

/-!
Article: jacobi, Theorem C.5.
Both original shifted energies converge uniformly on every compact
slit-domain set: the complex square and the distinct modulus square.
All finite arrays use the actual shifted finite spectral diagonal;
the direct complex-matrix identity supplies its original resolvent form.
Use: the two different square-error inequalities give both genuine uniform shifted energy integrands required by Theorem C.5.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Comparison
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual uniform finite shifted-profile error times the genuine
sum of the two original norms vanishes uniformly on the entire physical
matrix range and each original compact shift set.
Use: the two different square-error inequalities give both genuine
uniform shifted energy integrands required by Theorem C.5.
Article: jacobi, Theorem C.5.
Proof: the actual finite and continuum profiles have proved common
compact bounds. Choose the original row tolerance below epsilon divided
by their sum plus one; multiply the true row error by that same bound. -/
theorem finiteShifted_square_budget {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i:Fin (n+1),∀w∈W,
      ‖finiteShiftedDiagonal a b ha hb n i w-shiftedProfile a ha (matrixPoint n i) w‖*
        (‖finiteShiftedDiagonal a b ha hb n i w‖+‖shiftedProfile a ha (matrixPoint n i) w‖)<ε := by
  -- The same budget controls the complex square and the modulus square.
  obtain ⟨B,hB,hfinite⟩ := finiteShiftedDiagonal_bound ha hb hW hsub
  obtain ⟨NB,hNB⟩ := eventually_atTop.mp hfinite
  obtain ⟨C,hC,hcontinuum⟩ := shiftedProfile_compact_bound a ha hW hsub
  intro ε hε
  let δ := ε/(B+C+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨ND,hND⟩ := finiteShiftedDiagonal_uniform ha hb hW hsub δ hδ
  refine ⟨max NB ND,fun n hn i w hw => ?_⟩
  have hsum : ‖finiteShiftedDiagonal a b ha hb n i w‖+‖shiftedProfile a ha (matrixPoint n i) w‖≤B+C :=
    add_le_add (hNB n (by omega) i w hw) (hcontinuum (matrixPoint n i) w hw)
  have hδeq : δ*(B+C+1)=ε := div_mul_cancel₀ _ (by positivity)
  calc
    _≤‖finiteShiftedDiagonal a b ha hb n i w-shiftedProfile a ha (matrixPoint n i) w‖*(B+C) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _<δ*(B+C) := mul_lt_mul_of_pos_right (hND n (by omega) i w hw) (by positivity)
    _<ε := by nlinarith

/-- The actual finite complex-square shifted energy converges uniformly
to the square integral of the same genuine original shifted profile.
Use: the direct complex matrix identity turns this into the first
N-cubed energy limit in Theorem C.5.
Article: jacobi, Theorem C.5.
Proof: the common actual square budget controls the complex square
error on every original physical sample. Exact full-cell integration
and compact continuous-family quadrature give the same original integral,
uniformly over the entire genuine compact shift parameter set. -/
theorem finiteShiftedSquare_energy_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      ‖(1/((n:ℝ)+1)) • (∑i:Fin (n+1),(finiteShiftedDiagonal a b ha hb n i w)^2)-
        (∫t:Interval,(shiftedProfile a ha t w)^2)‖<ε := by
  -- The scalar square is complex; no conjugation is introduced in this first energy.
  let _ : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let G : C(Interval×W,ℂ) := ⟨fun p => (shiftedProfile a ha p.1 p.2)^2,
    (shiftedProfile_joint_continuous a ha hW hsub).pow 2⟩
  have hh := compact_full_mesh_integral G
    (fun n i (w:W) => (finiteShiftedDiagonal a b ha hb n i w)^2) (by
      intro ε hε
      obtain ⟨N,hN⟩ := finiteShifted_square_budget ha hb hW hsub ε hε
      exact ⟨N,fun n hn i w => (complex_square_error _ _).trans_lt (hN n hn i w w.property)⟩)
  intro ε hε
  obtain ⟨N,hN⟩ := hh ε hε
  exact ⟨N,fun n hn w hw => hN n hn ⟨w,hw⟩⟩

/-- The distinct actual finite modulus-square shifted energy converges
uniformly to the squared-norm integral of the same original shifted profile.
Use: the direct complex matrix identity gives the second N-cubed energy
limit of Theorem C.5, with the modulus retained exactly.
Article: jacobi, Theorem C.5.
Proof: use the true squared-norm difference estimate with the same
proved uniform square budget. Exact original full-cell integration and
compact-family quadrature preserve both the true finite normalization
and the full original compact-parameter uniformity. -/
theorem finiteShiftedNormSquare_energy_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      |(∑i:Fin (n+1),‖finiteShiftedDiagonal a b ha hb n i w‖^2)/((n:ℝ)+1)-
        (∫t:Interval,‖shiftedProfile a ha t w‖^2)|<ε := by
  -- This second energy is real and uses squared moduli, unlike the first complex energy.
  let _ : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let G : C(Interval×W,ℝ) := ⟨fun p => ‖shiftedProfile a ha p.1 p.2‖^2,
    (shiftedProfile_joint_continuous a ha hW hsub).norm.pow 2⟩
  have hh := compact_full_mesh_integral G
    (fun n i (w:W) => ‖finiteShiftedDiagonal a b ha hb n i w‖^2) (by
      intro ε hε
      obtain ⟨N,hN⟩ := finiteShifted_square_budget ha hb hW hsub ε hε
      refine ⟨N,fun n hn i w => ?_⟩
      rw [Real.norm_eq_abs]
      exact (norm_square_error _ _).trans_lt (hN n hn i w w.property))
  intro ε hε
  obtain ⟨N,hN⟩ := hh ε hε
  refine ⟨N,fun n hn w hw => ?_⟩
  simpa only [G,ContinuousMap.coe_mk,smul_eq_mul,one_div,mul_comm,one_mul,Real.norm_eq_abs,div_eq_mul_inv] using hN n hn ⟨w,hw⟩

end
end jacobi.EdgeResolvent
