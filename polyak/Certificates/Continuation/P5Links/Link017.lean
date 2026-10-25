import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch017
import polyak.Certificates.Continuation.P5Batches.Batch018

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 17. -/
namespace polyak.Certificates.Continuation.P5.Link017
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch017.C0 Batch018.C0
    Batch017.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link017
