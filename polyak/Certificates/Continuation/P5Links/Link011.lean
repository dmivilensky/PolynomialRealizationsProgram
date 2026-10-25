import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch011
import polyak.Certificates.Continuation.P5Batches.Batch012

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 11. -/
namespace polyak.Certificates.Continuation.P5.Link011
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch011.C0 Batch012.C0
    Batch011.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link011
