import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch001
import polyak.Certificates.Continuation.P5Batches.Batch002

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 1. -/
namespace polyak.Certificates.Continuation.P5.Link001
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch001.C0 Batch002.C0
    Batch001.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link001
