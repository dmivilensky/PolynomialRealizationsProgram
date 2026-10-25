import polyak.CertifiedExamples.Exact313.SystemCode
import polyak.CertifiedExamples.Trigonometry
import polyak.CertifiedExamples.Exact313.GeometryCode
import polyak.Certificates.PartII.Exact313.Root

namespace polyak.Certificates.PartII.Exact313.System
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric
open polyak.CertifiedExamples.Exact313

def certificate : WeightedCertificate 3 where
  center := ![(4892597594341437302122239418737277510899/5000000000000000000000000000000000000000),(490575484012851398768790723828157656367/250000000000000000000000000000000000000),(-3012089680426392103854814868090438098803/1000000000000000000000000000000000000000)]
  radius := ![(1/100000000),(1/100000000),(1/100000000)]
  preconditioner := !![(16208628363692150658789203395051/1000000000000000000000000000000000),(18386817185629678949774691284151/50000000000000000000000000000000),(-1192211993361905223941216354183/50000000000000000000000000000000);(-11355632723829328290293821843439/1000000000000000000000000000000),(-15448653577849518812403574521211/25000000000000000000000000000000),(22594348405232324122770873793911/10000000000000000000000000000000);(1538598199885489335845112673633/50000000000000000000000000000),(-21024880918584376676366250093259/5000000000000000000000000000000),(-33133567708016145170860693493983/5000000000000000000000000000000)]

def config : DyadicConfig := {precision:=-192,taylorDepth:=40}

theorem accepted : checkDyadic SystemCode.equations
    polyak.CertifiedExamples.Trigonometry.piTight certificate config=true := by
  kernel_decide

theorem nonsingular : SystemCode.nonsingularCheck
    polyak.CertifiedExamples.Trigonometry.piTight
    (coordinateBox certificate.center certificate.radius)
    certificate.preconditioner config=true := by
  kernel_decide

theorem coefficient_lower_0 : boundCheck (.sub Code.constant (.const (coordinateBox certificate.center certificate.radius 0).lo))
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

theorem coefficient_upper_0 : boundCheck (.sub (.const (coordinateBox certificate.center certificate.radius 0).hi) Code.constant)
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

theorem coefficient_lower_1 : boundCheck (.sub Code.linear (.const (coordinateBox certificate.center certificate.radius 1).lo))
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

theorem coefficient_upper_1 : boundCheck (.sub (.const (coordinateBox certificate.center certificate.radius 1).hi) Code.linear)
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

theorem coefficient_lower_2 : boundCheck (.sub Code.quadratic (.const (coordinateBox certificate.center certificate.radius 2).lo))
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

theorem coefficient_upper_2 : boundCheck (.sub (.const (coordinateBox certificate.center certificate.radius 2).hi) Code.quadratic)
    polyak.Certificates.PartII.Exact313.piBox
    (coordinateBox polyak.Certificates.PartII.Exact313.certificate.center
      polyak.Certificates.PartII.Exact313.certificate.radius)
    polyak.Certificates.PartII.Exact313.config true=true := by
  kernel_decide

end polyak.Certificates.PartII.Exact313.System
