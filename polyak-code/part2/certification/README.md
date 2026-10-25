# Part II exact mathematical witnesses

This component constructs exact witnesses for five examples: the rational
period-13 divergence tuning, the rational convergence tuning in the fourth
gap, the exact two-lag 3/13 contact point, and the two mixed-spectrum
plateaus with anchors 2/9 and 5/21.

From the [package root](../../README.md), using the pinned
[dependencies](../../requirements.txt), run:

```sh
python verify_all.py --part2-only
```

This reconstructs the witnesses from their source formulas and writes
`part2/proof/proof.tar.xz`. The full `python verify_all.py` command also
creates this archive. To run its data construction directly:

```sh
python -m part2.certification regen
```

The modules compute rational polynomial coefficients, root brackets,
preconditioners, trigonometric enclosures, normalized adjugate kernels,
Cramer slope moments, positive lifted weights and finite polynomial covers.
The data retain the signed lags, source parameter values and interval bounds
needed for compact exact checking. See the [data contract](../proof/README.md).

Figure generation is available through `python figures/make_all.py`.
