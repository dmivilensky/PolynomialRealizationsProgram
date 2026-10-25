import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch015
import polyak.Certificates.Continuation.P5Batches.Batch016

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 15. -/
namespace polyak.Certificates.Continuation.P5.Link015
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch015.C0 Batch016.C0
    Batch015.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link015
