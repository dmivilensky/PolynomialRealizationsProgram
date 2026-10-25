import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch007
import polyak.Certificates.Continuation.P5Batches.Batch008

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 7. -/
namespace polyak.Certificates.Continuation.P5.Link007
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch007.C0 Batch008.C0
    Batch007.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link007
