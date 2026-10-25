import polyak.CertifiedExamples.Exact313.GeometryCode
import polyak.Certificates.PartII.Exact313.Root

/-! Every concrete reserve is independently recomputed by the kernel. -/
namespace polyak.Certificates.PartII.Exact313
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric

theorem reserve00 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 0)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve01 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 1)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve02 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 2)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve03 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 3)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve04 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 4)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve05 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 5)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve06 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 6)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve07 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 7)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve08 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 8)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve09 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 9)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve10 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 10)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve11 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 11)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve12 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 12)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve13 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 13)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve14 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 14)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve15 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 15)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem reserve16 : boundCheck
    (polyak.CertifiedExamples.Exact313.Code.reserves 16)
    piBox (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

end polyak.Certificates.PartII.Exact313
