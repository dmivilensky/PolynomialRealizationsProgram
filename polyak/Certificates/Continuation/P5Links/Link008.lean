import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch008
import polyak.Certificates.Continuation.P5Batches.Batch009

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 8. -/
namespace polyak.Certificates.Continuation.P5.Link008
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch008.C0 Batch009.C0
    Batch008.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link008
