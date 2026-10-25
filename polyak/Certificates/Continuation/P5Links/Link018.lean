import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch018
import polyak.Certificates.Continuation.P5Batches.Batch019

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 18. -/
namespace polyak.Certificates.Continuation.P5.Link018
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch018.C0 Batch019.C0
    Batch018.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link018
