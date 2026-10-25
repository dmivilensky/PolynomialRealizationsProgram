import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch014
import polyak.Certificates.Continuation.P5Batches.Batch015

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 14. -/
namespace polyak.Certificates.Continuation.P5.Link014
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch014.C0 Batch015.C0
    Batch014.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link014
