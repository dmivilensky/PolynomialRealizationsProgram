import polyak.Numerics.Parametric.CorrelatedEndpoint
import polyak.Certificates.Continuation.P5Batches.Batch010
import polyak.Certificates.Continuation.P5Batches.Batch011

/-! Article: Appendix B P5 continuation, exact adjacent-box transfer 10. -/
namespace polyak.Certificates.Continuation.P5.Link010
open Numerics.Parametric

theorem accepted : checkCorrelatedEndpoint P5.system Batch010.C0 Batch011.C0
    Batch010.I0.hi {precision:=-80}=true := by kernel_decide

end polyak.Certificates.Continuation.P5.Link010
