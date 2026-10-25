import polyak.Certificates.Continuation.P1Cover
import polyak.Numerics.Parametric.DyadicAnalytic

/-! An actual source root at every point of the complete checked P1 interval. -/
noncomputable section
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric Filter
open scoped Topology

def continuationDomain : Set ℝ := Set.Icc 0 (733/1000)

structure CheckedPoint (z : ℝ) where
  slab : Slab 2
  mem : slab∈polyak.Certificates.Continuation.P1.slabs
  parameter : z∈slab.domain
  position : Coordinates
  box : FinBoxMem position (coordinateBox slab.certificate.center slab.certificate.radius)
  source : regularSystem (z,position)=0

private theorem checkedPoint_exists (z : ℝ) (hz : z∈continuationDomain) : Nonempty (CheckedPoint z) := by
  obtain ⟨slab,hm,hs,x,hx,_⟩ := polyak.Certificates.Continuation.P1.source_roots hz
  exact ⟨⟨slab,hm,hs,x,hx.1,hx.2⟩⟩

def checkedPoint (z : ℝ) (hz : z∈continuationDomain) : CheckedPoint z :=
  Classical.choice (checkedPoint_exists z hz)

/-- A selection of actual roots; subsequent algebraic uniqueness removes every choice. -/
def continuation (z : ℝ) : Coordinates := by
  classical
  exact if hz : z∈continuationDomain then (checkedPoint z hz).position else criticalPoint

theorem continuation_eq_point {z : ℝ} (hz : z∈continuationDomain) :
    continuation z=(checkedPoint z hz).position := by simp only [continuation,dite_eq_left hz]

theorem continuation_source {z : ℝ} (hz : z∈continuationDomain) :
    regularSystem (z,continuation z)=0 := by
  rw [continuation_eq_point hz]
  exact (checkedPoint z hz).source

theorem continuation_zero : continuation 0=criticalPoint := by
  apply criticalPoint_unique
  exact continuation_source (by norm_num [continuationDomain])

/-- Every selected point has a genuine analytic implicit source extension. -/
theorem continuation_local_extension {z : ℝ} (hz : z∈continuationDomain) :
    ∃ g : ℝ → Coordinates, AnalyticAt ℝ g z ∧ g z=continuation z ∧
      ∀ᶠ r in 𝓝 z, regularSystem (r,g r)=0 := by
  let p := checkedPoint z hz
  have hc : checkDyadic polyak.Certificates.Continuation.P1.system p.slab.domain p.slab.certificate
      {precision:=-80}=true :=
    List.all_eq_true.mp polyak.Certificates.Continuation.P1.accepted p.slab p.mem
  have hs : system polyak.Certificates.Continuation.P1.system z p.position=0 := by
    rw [polyak.Certificates.Continuation.P1.source_system]
    exact p.source
  obtain ⟨g,hg,hself,heq⟩ := checkDyadic_analytic_branch
    polyak.Certificates.Continuation.P1.system p.slab.domain p.slab.certificate
      {precision:=-80} hc p.parameter p.box hs
  refine ⟨g,hg,?_,?_⟩
  · rw [continuation_eq_point hz]
    exact hself
  · filter_upwards [heq] with r hr
    rwa [polyak.Certificates.Continuation.P1.source_system] at hr

end polyak.Boundary.P1
