import chebyshev2.Certificates.Compact.ReferenceResidualData
import chebyshev2.Numerics.IntegerReferenceTrajectory

/-!
Article: chebyshev2, Section 4.1.
Complete actual reference trajectory on both halves.
Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.right_chain` feeds
`chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` (full trajectory).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Certificates.Compact.ReferenceTrajectory
noncomputable section
open Set chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
open chebyshev2.Certificates.DualInputs
open ReferenceResiduals
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/--
Defines `leftRows` of type `List ResidualCell.Row` by `rows.take 1228`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.left_chain` uses this definition
to establish acceptance/decoding identity for the displayed finite data:
`ResidualCell.chainCheck scale eta leftBound scale 0 0 0 leftRows=true`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def leftRows : List ResidualCell.Row := rows.take 1228
/--
Defines `rightRows` of type `List ResidualCell.Row` by `rows.drop 1228`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.right_chain` uses this definition
to establish acceptance/decoding identity for the displayed finite data:
`ResidualCell.chainCheck scale eta rightBound (2*scale) scale (ResidualCell.lastValue scale 0
leftRows) leftBound rightRows=true`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rightRows : List ResidualCell.Row := rows.drop 1228
/--
Defines `leftBound` of type `ℚ` by `2/10^14`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.left_chain` uses this definition
to establish acceptance/decoding identity for the displayed finite data:
`ResidualCell.chainCheck scale eta leftBound scale 0 0 0 leftRows=true`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def leftBound : ℚ := 2/10^14
/--
Defines `rightBound` of type `ℚ` by `4/10^14`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.right_chain` uses this definition
to establish acceptance/decoding identity for the displayed finite data:
`ResidualCell.chainCheck scale eta rightBound (2*scale) scale (ResidualCell.lastValue scale 0
leftRows) leftBound rightRows=true`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def rightBound : ℚ := 4/10^14

/--
Exact identity `leftRows++rightRows=rows`.

Use: `chebyshev2.Certificates.Compact.ContactValues.ValidPanel.actual` rewrites with this
identity to establish `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem split_rows : leftRows++rightRows=rows := List.take_append_drop _ _
/--
Acceptance/decoding identity for the displayed finite data: `leftRows.all
(ResidualCell.leftChartCheck scale)=true`.

Use: `chebyshev2.Certificates.Compact.ContactValues.ValidPanel.actual` uses this identity
to establish `(p.valuePanel scale epsilon).Actual scale
((ReferenceJetSource.referenceData reference).directContactCore (σ := (sigma:ℝ)) (by
exact_mod_cast reference_signs.1))`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem left_charts : leftRows.all (ResidualCell.leftChartCheck scale)=true := by decide +kernel
/--
Acceptance/decoding identity for the displayed finite data: `rightRows.all
(ResidualCell.rightChartCheck scale)=true`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` uses this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem right_charts : rightRows.all (ResidualCell.rightChartCheck scale)=true := by decide +kernel
/--
Acceptance/decoding identity for the displayed finite data: `ResidualCell.chainCheck scale eta
leftBound scale 0 0 0 leftRows=true`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` uses this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem left_chain : ResidualCell.chainCheck scale eta leftBound scale 0 0 0 leftRows=true := by
  decide +kernel
/--
Acceptance/decoding identity for the displayed finite data: `ResidualCell.chainCheck scale eta
rightBound (2*scale) scale (ResidualCell.lastValue scale 0 leftRows) leftBound rightRows=true`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.full_trajectory` uses this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem right_chain : ResidualCell.chainCheck scale eta rightBound (2*scale) scale
    (ResidualCell.lastValue scale 0 leftRows) leftBound rightRows=true := by decide +kernel


/--
Defines `timeBox` of type `Bounds` by `⟨r.start,r.start+r.width⟩`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.covers` uses this definition to
establish constructs witnesses with the exact properties `∃ r∈rows, t∈Icc (r.left scale)
(r.right scale)`.

Article: chebyshev2, Section 4.1.
-/
def timeBox (r : ResidualCell.Row) : Bounds := ⟨r.start,r.start+r.width⟩
/--
Acceptance/decoding identity for the displayed finite data: `partitionCheck 0 (2*scale)
(rows.map timeBox)=true`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.covers` uses this identity to
establish constructs witnesses with the exact properties `∃ r∈rows, t∈Icc (r.left scale)
(r.right scale)`.

Article: chebyshev2, Section 4.1.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem partition : partitionCheck 0 (2*scale) (rows.map timeBox)=true := by decide +kernel
/--
The precise assertion is `rows≠[]`.

Use: `chebyshev2.Certificates.Compact.ReferenceTrajectory.covers` uses this assertion to
establish constructs witnesses with the exact properties `∃ r∈rows, t∈Icc (r.left scale)
(r.right scale)`.

Article: chebyshev2, Section 4.1.

Proof: Reduce the finite acceptance proposition in Lean's kernel. This verifies literal data
against the proved checker; a generator's numerical report is not a premise.
-/
theorem rows_nonempty : rows≠[] := by decide +kernel

/--
Constructs witnesses with the exact properties `∃ r∈rows, t∈Icc (r.left scale) (r.right
scale)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.partitionCheck_cover`,
`chebyshev2.Certificates.Compact.ReferenceTrajectory.partition`,
`chebyshev2.Certificates.Compact.ReferenceTrajectory.rows_nonempty` with the arguments
shown in the proof.
-/
theorem covers {t : ℝ} (ht : t∈Icc (0:ℝ) 2) :
    ∃ r∈rows, t∈Icc (r.left scale) (r.right scale) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.partitionCheck_cover`,
  -- `chebyshev2.Certificates.Compact.ReferenceTrajectory.partition`,
  -- `chebyshev2.Certificates.Compact.ReferenceTrajectory.rows_nonempty` with the arguments
  -- shown in the proof.
  have hs : (0:ℝ)<scale := by norm_num [scale]
  obtain ⟨box,hbox,htbox⟩ := partitionCheck_cover (s := scale) partition
    (by
      intro h
      apply rows_nonempty
      have hh := congrArg List.length h
      simp only [List.length_map,List.length_nil] at hh
      exact List.length_eq_zero_iff.mp hh) (x := t)
    (by simpa using mul_nonneg hs.le ht.1)
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left ht.2 hs.le)
  obtain ⟨r,hr,hrbox⟩ := List.mem_map.mp hbox
  subst box
  refine ⟨r,hr,?_⟩
  dsimp [timeBox,Bounds.Mem] at htbox
  simp only [ResidualCell.Row.left,ResidualCell.Row.right,mem_Icc,
    div_le_iff₀ hs,le_div_iff₀ hs]
  simpa only [Int.cast_add,Int.cast_natCast,mul_comm] using htbox

end
end chebyshev2.Certificates.Compact.ReferenceTrajectory
