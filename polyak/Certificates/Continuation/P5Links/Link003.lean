import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch003
import polyak.Certificates.Continuation.P5Batches.Batch004

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 3. -/
namespace polyak.Certificates.Continuation.P5.Link003
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch003.C0 Batch004.C0
    Batch003.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link003
