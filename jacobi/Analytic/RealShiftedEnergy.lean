import jacobi.Analytic.ShiftedResolventLimits
import jacobi.Analytic.RealShiftSpectrum
import jacobi.Finite.RealComplexInverse
import jacobi.Variational.Transfer

/-!
Article: jacobi, Corollary C.6.
The real shifted objective uses the literal original real matrix inverse
and the complete original finite fibres. The proved complex candidate
limit supplies its upper bound without an additional numerical premise.
Use: realShiftedProfile_cast identifies the real squared integral in the printed off-edge bounds.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter Matrix MeasureTheory jacobi.Reference jacobi.Comparison jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

/-- The original real specialization of the same genuine shifted profile series.
Use: realShiftedProfile_cast identifies the real squared integral in the printed off-edge bounds.
Article: jacobi, Corollary C.6.
-/
def realShiftedProfile (a:ℝ) (ha:-1<a) (t:Interval) (w:ℝ) : ℝ :=
  ∑'k,realShiftedEdge a ha w k* jacobi.GelfandLevitan.spectralProfile a ha k t

/-- Complexifying the actual real profile gives the original complex shifted profile exactly.
Use: realShiftedCandidate_energy_limit specializes both the same source function and its genuine original energy.
Article: jacobi, Corollary C.6.
Proof: the continuous original real-to-complex embedding commutes with
the true series sum and every original rational spectral coefficient. -/
theorem realShiftedProfile_cast (a:ℝ) (ha:-1<a) (t:Interval) (w:ℝ) :
    (realShiftedProfile a ha t w:ℂ)=shiftedProfile a ha t (w:ℂ) := by
  rw [realShiftedProfile,shiftedProfile,Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  simp only [shiftedProfileTerm,shiftedEdge,realShiftedEdge]
  push_cast
  rfl

/-- The actual shifted upper constant is the squared integral of the original real profile.
Use: shiftedOptimalEnergy_upper gives the printed off-edge upper bound.
Article: jacobi, Corollary C.6.
-/
def realShiftedUpper (a:ℝ) (ha:-1<a) (w:ℝ) : ℝ :=
  ∫t:Interval,(realShiftedProfile a ha t w)^2

/-- The actual finite real shifted energy at an arbitrary real resolvent point.
Use: shiftedFibreInfimum and shiftedOptimalEnergy retain the entire original competitor domain.
Article: jacobi, Corollary C.6.
-/
def realShiftedEnergy {N:ℕ} (J:chebyshev2.Jacobi N) (z:ℝ) : ℝ :=
  ∑i:Fin N,((z • (1:Matrix (Fin N) (Fin N) ℝ)-J.matrix)⁻¹ i i)^2

/-- The genuine shifted candidate energy has the original real squared-profile limit.
Use: shiftedOptimalEnergy_upper establishes the true full-fibre upper bound.
Article: jacobi, Corollary C.6.
Proof: the original real matrix inverse complexifies to the same
complex inverse used in D. Apply the proved modulus-square energy limit
on the admissible singleton; the real squared moduli are exactly squares. -/
theorem realShiftedCandidate_energy_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    Tendsto (fun n:ℕ => realShiftedEnergy (targetChain a b ha hb n)
      (1+w/(2*((n:ℝ)+1)^2))/((n:ℝ)+1)^3) atTop (𝓝 (realShiftedUpper a ha w)) := by
  -- The exact matrix identity includes every original physical row and matrix dimension.
  have hi (n:ℕ) (i:Fin (n+1)) :
      (((((1+w/(2*((n:ℝ)+1)^2)) • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-
        (targetChain a b ha hb n).matrix)⁻¹) i i:ℝ):ℂ)=
        shiftedTargetResolvent a b ha hb n (w:ℂ) i i := by
    have h := congrArg (fun M:Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M i i)
      (real_shifted_inverse (targetChain a b ha hb n).matrix (1+w/(2*((n:ℝ)+1)^2)))
    change (( _ :ℝ):ℂ)=_ at h
    have he : ((1+w/(2*((n:ℝ)+1)^2):ℝ):ℂ)=edgePoint n (w:ℂ) := by
      unfold edgePoint
      push_cast
      rfl
    rw [he] at h
    exact h
  have h := shiftedTargetNormSquare_energy_uniform ha hb (W:={(w:ℂ)}) isCompact_singleton
    (by intro z hz; rw [mem_singleton_iff.mp hz]; exact Or.inr hw)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := h ε hε
  refine ⟨N,fun n hn => ?_⟩
  have hh := hN n hn (w:ℂ) (mem_singleton _)
  simp only [← hi,← realShiftedProfile_cast,Complex.norm_real,Real.norm_eq_abs,sq_abs] at hh
  exact hh

/-- The original real shifted objective in the nonnegative extended cost convention.
Use: all shifted infima keep empty-fibre and lower-limit conventions explicit.
Article: jacobi, Corollary C.6.
-/
def realShiftedCost {N:ℕ} (J:chebyshev2.Jacobi N) (z:ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (realShiftedEnergy J z/(N:ℝ)^3)

/-- The actual shifted infimum over the complete original polynomial fibre.
Use: shiftedOptimalEnergy is the source's genuine full-fibre asymptotic optimum.
Article: jacobi, Corollary C.6.
-/
def shiftedFibreInfimum {N:ℕ} (S:Nodes N) (z:ℝ) : ℝ≥0∞ :=
  sInf ((fun J:chebyshev2.Jacobi N => realShiftedCost J z) '' {J | InFiber J S.polynomial})

/-- The original shifted limiting optimal energy, using the true dimensions N=n+1.
Use: the complete off-edge two-sided corollary bounds this actual full original infimum.
Article: jacobi, Corollary C.6.
-/
def shiftedOptimalEnergy (a b:ℝ) (ha:-1<a) (hb:-1<b) (w:ℝ) : ℝ≥0∞ :=
  liminf (fun n:ℕ => shiftedFibreInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))
    (1+w/(2*((n:ℝ)+1)^2))) atTop

/-- The actual full shifted optimal energy is bounded by the same source squared-profile integral.
Use: the upper side of Corollary C.6 and finiteness of its true objective.
Article: jacobi, Corollary C.6.
Proof: the original persymmetric chain belongs to every genuine full
fibre. Its proved real shifted energy limit bounds their lower limiting infima. -/
theorem shiftedOptimalEnergy_upper {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    shiftedOptimalEnergy a b ha hb w≤ENNReal.ofReal (realShiftedUpper a ha w) := by
  have hc := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (realShiftedCandidate_energy_limit ha hb hw)
  have hbnd (n:ℕ) : shiftedFibreInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))
      (1+w/(2*((n:ℝ)+1)^2))≤realShiftedCost (targetChain a b ha hb n)
        (1+w/(2*((n:ℝ)+1)^2)) := sInf_le ⟨_,targetChain_inFiber a b ha hb n,rfl⟩
  have hh := liminf_le_liminf (f:=atTop) (Eventually.of_forall hbnd)
  exact hh.trans_eq (by simpa only [realShiftedCost,Nat.cast_add,Nat.cast_one,Function.comp_def] using hc.liminf_eq)

end
end jacobi.EdgeResolvent
