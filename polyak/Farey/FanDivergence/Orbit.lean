import polyak.Levels.Realization.AtomicOrbit
import polyak.Levels.Realization.ExactThreshold

/-! A finite fan program produces the literal from-rest heavy-ball
executor, in exactly twice the number of positive weights plus one dimensions. -/
noncomputable section
namespace polyak.Farey
open polyak.General polyak.Levels Dynamics MeasureTheory Filter
open scoped Topology

def FanPeriodicOrbit (q : Tuning) (k r : ℕ) : Prop :=
  ∃f : EuclideanSpace ℝ (Fin (2*r+1))→ℝ,
    CenteredSmoothStronglyConvex q.x q.y f ∧
    ∃x₀,x₀≠0 ∧ ∃c₀ : ℝ,0<c₀ ∧
    ∃orbit : ℕ→EuclideanSpace ℝ (Fin (2*r+1)),
      Function.Periodic orbit k ∧
      (∀n,c₀*‖x₀‖≤‖iterate (gradient f) 1 q.beta x₀ n‖) ∧
      Tendsto (fun n=>iterate (gradient f) 1 q.beta x₀ n-orbit n) atTop (𝓝 0)

theorem fan_divergence_of_weights (q : Tuning) {J : Type*} [Fintype J]
    {k : ℕ} (hk : 0<k) (w : J→NNReal) (a : J→Frequency)
    (hw : 0<∑j,w j) (ha : ∀j,a j∈periodicGrid k)
    (hmin : 0≤∑j,(w j:ℝ)*(tuningCurve q).minimizer (a j))
    (hlag : ∀n : ℕ,0<n→n<k→0≤∑j,(w j:ℝ)*(tuningCurve q).lag (n:ℤ) (a j)) :
    FanPeriodicOrbit q k (Fintype.card {j // 0<w j}) ∧ 1≤q.rate := by
  have hs : ProgramSolution (tuningCurve q) nonzeroLags (atomicMeasure w a) :=
    (atomic_program_iff (tuningCurve q) hk w a hw ha).mpr ⟨hmin,hlag⟩
  exact ⟨atomic_periodic_orbit_positive_count q w a hw ha hs,fp_one_le_rate q ⟨_,hs⟩⟩

theorem fan_divergence_of_real_weights (q : Tuning) {J : Type*} [Fintype J]
    {k : ℕ} (hk : 0<k) (w : J→ℝ) (a : J→Frequency)
    (hw : ∀j,0≤w j) (hne : ∃j,0<w j) (ha : ∀j,a j∈periodicGrid k)
    (hmin : 0≤∑j,w j*(tuningCurve q).minimizer (a j))
    (hlag : ∀n : ℕ,0<n→n<k→0≤∑j,w j*(tuningCurve q).lag (n:ℤ) (a j)) :
    FanPeriodicOrbit q k (Fintype.card {j // 0<w j}) ∧ 1≤q.rate := by
  classical
  let v : J→NNReal := fun j=>⟨w j,hw j⟩
  have hv : 0<∑j,v j := by
    obtain ⟨j,hj⟩ := hne
    exact lt_of_lt_of_le hj (Finset.single_le_sum (fun _ _=>zero_le) (Finset.mem_univ j))
  exact fan_divergence_of_weights q hk v a hv ha hmin hlag

end polyak.Farey
