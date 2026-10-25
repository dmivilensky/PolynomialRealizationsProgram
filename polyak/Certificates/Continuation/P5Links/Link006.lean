import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch006
import polyak.Certificates.Continuation.P5Batches.Batch007

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 6. -/
namespace polyak.Certificates.Continuation.P5.Link006
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch006.C0 Batch007.C0
    Batch006.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link006
