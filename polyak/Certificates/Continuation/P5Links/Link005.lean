import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch005
import polyak.Certificates.Continuation.P5Batches.Batch006

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 5. -/
namespace polyak.Certificates.Continuation.P5.Link005
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch005.C0 Batch006.C0
    Batch005.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link005
