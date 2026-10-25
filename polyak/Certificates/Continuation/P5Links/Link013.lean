import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch013
import polyak.Certificates.Continuation.P5Batches.Batch014

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 13. -/
namespace polyak.Certificates.Continuation.P5.Link013
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch013.C0 Batch014.C0
    Batch013.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link013
