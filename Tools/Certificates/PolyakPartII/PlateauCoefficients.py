"""Exact coefficient and gap acceptance checks for the selected plateau rows."""
from pathlib import Path

OUTPUTS=frozenset({'polyak/Certificates/PartII/Plateaus/CoefficientChecks.lean'})


def generate(payload,stagingRoot):
    if (not isinstance(payload,dict) or payload.get('schema')!='heavy-ball-selected-plateaus-v1'
            or {r['name'] for r in payload['rows']}!={'2/9','5/21'}):
        raise ValueError('invalid selected plateau coefficient source')
    lines=['import polyak.CertifiedExamples.Plateaus.CoefficientBounds',
           'import polyak.Certificates.PartII.Plateaus.Data','',
           '/-! Independent rejecting arithmetic checks for actual Xi coefficients and I4. -/',
           'namespace polyak.Certificates.PartII.Plateaus',
           'open polyak.CertifiedExamples.Plateaus chebyshev2.Numerics','']
    for L in (18,21):
        tag=f'row{L}'
        for i in range(3):
            lines += [f'theorem {tag}_coefficient{i}_checked :',
                      f'    enclosed (coefficientExpr {tag}Y {tag}Beta {i}) (coefficientBox {tag}Kappa) ({tag}Xi {i})=true :=',
                      '  by kernel_decide','']
        lines += [f'theorem {tag}_coefficients_checked :',
                  f'    ∀i,enclosed (coefficientExpr {tag}Y {tag}Beta i) (coefficientBox {tag}Kappa) ({tag}Xi i)=true := by',
                  '  intro i','  fin_cases i']
        lines += [f'  · exact {tag}_coefficient{i}_checked' for i in range(3)]
        lines += ['']
        for i in range(5):
            lines += [f'theorem {tag}_gap{i}_checked :',
                      f'    (IntervalExpr.neg (gapTestExpr {i})).strictNegative {tag}Xi=true := by kernel_decide','']
        lines += [f'theorem {tag}_gap_checked :',
                  f'    ∀i,(IntervalExpr.neg (gapTestExpr i)).strictNegative {tag}Xi=true := by',
                  '  intro i','  fin_cases i']
        lines += [f'  · exact {tag}_gap{i}_checked' for i in range(5)]
        lines += ['']
    lines += ['end polyak.Certificates.PartII.Plateaus','']
    relative=next(iter(OUTPUTS));path=Path(stagingRoot)/relative
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text('\n'.join(lines),encoding='utf-8')
    return sorted(OUTPUTS)
