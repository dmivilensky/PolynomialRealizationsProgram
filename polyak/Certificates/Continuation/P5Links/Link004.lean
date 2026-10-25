import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch004
import polyak.Certificates.Continuation.P5Batches.Batch005

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 4. -/
namespace polyak.Certificates.Continuation.P5.Link004
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch004.C0 Batch005.C0
    Batch004.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link004
