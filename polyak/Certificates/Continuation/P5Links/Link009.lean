import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch009
import polyak.Certificates.Continuation.P5Batches.Batch010

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 9. -/
namespace polyak.Certificates.Continuation.P5.Link009
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch009.C0 Batch010.C0
    Batch009.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link009
