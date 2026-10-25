import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch012
import polyak.Certificates.Continuation.P5Batches.Batch013

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 12. -/
namespace polyak.Certificates.Continuation.P5.Link012
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch012.C0 Batch013.C0
    Batch012.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link012
