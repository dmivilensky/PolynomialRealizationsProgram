"""Cache immutable chronological Gram overlaps for observed secants."""

import numpy as np


class WindowGram:
    """Reuse immutable overlaps; append costs O(n m), instead of recomputing O(n m^2).

    Pair arrays are kept by reference, so object identity is safe from id recycling.
    Dropping any old pairs just takes the corresponding principal submatrix.
    """

    def __init__(self):
        self.pairs = []
        self.matrix = np.empty((0, 0))

    def get(self, S, Y, *, Sm=None, Ym=None):
        """Reuse chronological overlaps and optional already stacked matrices.

        XR retains a suffix and appends immutable pairs. That case copies a
        single old principal block; the general identity-based path below
        still supports arbitrary retained subsets. The indexed BLAS operands
        have the original shapes and layout, preserving their arithmetic.
        """
        p = len(S)
        shared = 0
        start = None
        if p and self.pairs:
            start = next(
                (i for i, (s, y) in enumerate(self.pairs) if s is S[0] and y is Y[0]), None
            )
            if start is not None:
                shared = min(len(self.pairs) - start, p)
                if any(
                    self.pairs[start + i][0] is not S[i] or self.pairs[start + i][1] is not Y[i]
                    for i in range(shared)
                ):
                    return self._general_get(S, Y, Sm=Sm, Ym=Ym)
                # An earlier old pair reintroduced after the suffix is a
                # reordering, not a new observation. Preserve its cached
                # overlaps through the general path as well.
                if start and any(
                    s is old_s and y is old_y
                    for s, y in zip(S[shared:], Y[shared:])
                    for old_s, old_y in self.pairs[:start]
                ):
                    return self._general_get(S, Y, Sm=Sm, Ym=Ym)
            # If the first pair is new but a later pair is old, this is an
            # arbitrary reordering rather than a chronological extension.
            elif any(
                s is old_s and y is old_y
                for s, y in zip(S[1:], Y[1:])
                for old_s, old_y in self.pairs
            ):
                return self._general_get(S, Y, Sm=Sm, Ym=Ym)
        M = np.empty((p, p))
        if shared:
            M[:shared, :shared] = self.matrix[start : start + shared, start : start + shared]
        if shared < p:
            Sm = np.column_stack(S) if Sm is None else Sm
            Ym = np.column_stack(Y) if Ym is None else Ym
            new, old = np.arange(shared, p), np.arange(shared)
            M[new, :] = Sm[:, new].T @ Ym
            if shared:
                M[:shared, shared:] = Sm[:, old].T @ Ym[:, new]
        self.pairs = list(zip(S, Y))
        self.matrix = M
        return M

    def _general_get(self, S, Y, *, Sm=None, Ym=None):
        lookup = {(id(s), id(y)): i for i, (s, y) in enumerate(self.pairs)}
        old, new, indices = [], [], []
        for j, (s, y) in enumerate(zip(S, Y)):
            i = lookup.get((id(s), id(y)))
            if i is None:
                new.append(j)
            else:
                old.append(j)
                indices.append(i)
        p = len(S)
        M = np.empty((p, p))
        if old:
            M[np.ix_(old, old)] = self.matrix[np.ix_(indices, indices)]
        if new:
            Sm = np.column_stack(S) if Sm is None else Sm
            Ym = np.column_stack(Y) if Ym is None else Ym
            M[new, :] = Sm[:, new].T @ Ym
            if old:
                M[np.ix_(old, new)] = Sm[:, old].T @ Ym[:, new]
        self.pairs = list(zip(S, Y))
        self.matrix = M
        return M
