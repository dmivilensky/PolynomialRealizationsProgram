import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch016
import polyak.Certificates.Continuation.P5Batches.Batch017

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 16. -/
namespace polyak.Certificates.Continuation.P5.Link016
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch016.C0 Batch017.C0
    Batch016.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link016
