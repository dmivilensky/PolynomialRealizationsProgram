import polyak.Boundary.P5.DerivativeContinuation
import polyak.Boundary.P5.EndpointJoin

/-! Article: the central dual weight has its correct sign on the whole
physical interval, from its actual strict derivative and exact endpoint. -/
namespace polyak.Boundary.P5
noncomputable section
open Set

theorem continuation_weight5_pos {h : ℝ} (hh : 0≤h) (hmax : h<P2.Ga-1) :
    0<1-Selection.continuation h 5-Selection.continuation h 6 := by
  have hm : h∈Icc (0 : ℝ) (11791/500000) :=
    ⟨hh,hmax.le.trans centralEndpoint_lt.le⟩
  have he : P2.Ga-1∈Icc (0 : ℝ) (11791/500000) :=
    ⟨centralEndpoint_pos.le,centralEndpoint_lt.le⟩
  have ho:=continuationWeight5_strictAntiOn hm he hmax
  simpa only [continuationWeight5,continuation_weight5_endpoint] using ho

theorem continuation_weight5_nonneg {h : ℝ} (hh : 0≤h) (hmax : h≤P2.Ga-1) :
    0≤1-Selection.continuation h 5-Selection.continuation h 6 := by
  rcases hmax.eq_or_lt with he|hl
  · rw [he,continuation_weight5_endpoint]
  · exact (continuation_weight5_pos hh hl).le

theorem continuation_weight5_eq_zero_iff {h : ℝ} (hh : 0≤h) (hmax : h≤P2.Ga-1) :
    1-Selection.continuation h 5-Selection.continuation h 6=0 ↔ h=P2.Ga-1 := by
  constructor
  · intro he
    by_contra hn
    exact (continuation_weight5_pos hh (lt_of_le_of_ne hmax hn)).ne' he
  · intro he
    rw [he,continuation_weight5_endpoint]

end
end polyak.Boundary.P5
