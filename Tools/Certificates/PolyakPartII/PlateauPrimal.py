"""Rejecting exact arithmetic checks for all essential primal residue signs."""
from pathlib import Path

OUTPUTS=frozenset({'polyak/Certificates/PartII/Plateaus/PrimalNumerical.lean'})


def generate(payload,stagingRoot):
    if (not isinstance(payload,dict) or payload.get('schema')!='heavy-ball-selected-plateaus-v1'
            or {r['name'] for r in payload['rows']}!={'2/9','5/21'}):
        raise ValueError('invalid selected primal source')
    lines=['import polyak.CertifiedExamples.Plateaus.PrimalExpressions',
           'import polyak.Certificates.PartII.Plateaus.Data','',
           '/-! Every non-tight residue and the actual source minimizer have strict positive signs. -/',
           'namespace polyak.Certificates.PartII.Plateaus',
           'open polyak.CertifiedExamples.Plateaus LeanCert.Core chebyshev2.Numerics','']
    for L,d,reps in [(18,2,[1,14]),(21,3,[1,9,17])]:
        tag=f'row{L}';dim=3+2*d
        vals=[f'{tag}Xi {i}' for i in range(3)]+[f'{tag}Cosines {i}' for i in range(d)]+[f'{tag}Right {i}' for i in range(d)]
        lines += [f'def {tag}PrimalBox : Fin {dim} → IntervalRat := !['+','.join(vals)+']','']
        X='![.variable 0,.variable 1,.variable 2]'
        C='!['+','.join(f'.variable {3+i}' for i in range(d))+']'
        P='!['+','.join(f'.variable {3+d+i}' for i in range(d))+']'
        lines += [f'def {tag}PrimalLagExpr (n:ℤ) : E {dim} :=',
                  f'  primalLag{d}Expr {X} {C} {P} n','',
                  f'def {tag}PrimalMinExpr : E {dim} :=',
                  f'  primalMin{d}Expr {X} {C} {P}','']
        for n in range(1,L):
            if n in reps:continue
            lines += [f'theorem {tag}_primal_lag{n:02d}_positive_checked :',
                      f'    (IntervalExpr.neg ({tag}PrimalLagExpr {n})).strictNegative {tag}PrimalBox=true := by kernel_decide','']
        lines += [f'theorem {tag}_inactive_checked : ∀n:Fin {L},0<n.val→'+''.join(f'n.val≠{r}→' for r in reps),
                  f'    (IntervalExpr.neg ({tag}PrimalLagExpr n.val)).strictNegative {tag}PrimalBox=true := by',
                  '  intro n hn '+ ' '.join(f'hn{r}' for r in reps),
                  '  fin_cases n']
        for n in range(L):
            if n==0 or n in reps:lines.append('  · norm_num at *')
            else:lines.append(f'  · exact {tag}_primal_lag{n:02d}_positive_checked')
        lines += ['',f'theorem {tag}_minimizer_positive_checked :',
                  f'    (IntervalExpr.neg {tag}PrimalMinExpr).strictNegative {tag}PrimalBox=true := by kernel_decide','']
    lines+=['end polyak.Certificates.PartII.Plateaus','']
    relative=next(iter(OUTPUTS));path=Path(stagingRoot)/relative
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text('\n'.join(lines),encoding='utf-8')
    return sorted(OUTPUTS)
