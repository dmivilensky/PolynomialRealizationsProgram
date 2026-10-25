import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch000
import polyak.Certificates.Continuation.P5Batches.Batch001

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 0. -/
namespace polyak.Certificates.Continuation.P5.Link000
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch000.C0 Batch001.C0
    Batch000.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link000
