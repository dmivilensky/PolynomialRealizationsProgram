"""Problem instances of Section 9: four graphs for gossip, and the smooth energy."""
import numpy as np
import networkx as nx


# ---------------------------------------------------------------- gossip
def _graph(name):
    if name == 'ring of cliques':
        return nx.ring_of_cliques(6, 8)
    if name == 'barbell':
        return nx.barbell_graph(12, 0)
    if name == 'geometric':
        return nx.random_geometric_graph(60, 0.25, seed=3)
    if name == 'grid':
        return nx.convert_node_labels_to_integers(nx.grid_2d_graph(8, 8))
    raise ValueError(name)


GRAPHS = ('ring of cliques', 'barbell', 'geometric', 'grid')


def gossip(name):
    """Incidence rows b_e = 1_i - 1_j, unit weights, Laplacian L = B^T B, and the
    spectral interval [lambda_2, lambda_max] of L on the complement of constants."""
    Gr = _graph(name)
    assert nx.is_connected(Gr)
    E = np.array(list(Gr.edges()))
    n = Gr.number_of_nodes()
    B = np.zeros((len(E), n))
    B[np.arange(len(E)), E[:, 0]] = 1.0
    B[np.arange(len(E)), E[:, 1]] = -1.0
    Lap = B.T @ B
    ev = np.linalg.eigvalsh(Lap)
    return B, np.ones(len(E)), Lap, ev[1], ev[-1]


# ---------------------------------------------------------------- smooth energy
def laplacian_1d(n):
    h = 1.0 / (n + 1)
    return (2 * np.eye(n) - np.eye(n, k=1) - np.eye(n, k=-1)) / h ** 2


def energy(n=63, load=100.0):
    """Minimizer u* of f(u) = u^T A u / 2 + sum u_i^4 / 4 - load * sum u_i
    (discretized -u'' + u^3 = load on (0,1), zero boundary values) and H* = A + 3 diag(u*^2)."""
    A = laplacian_1d(n)
    c = load * np.ones(n)
    u = np.zeros(n)
    for _ in range(60):
        step = np.linalg.solve(A + np.diag(3 * u ** 2), A @ u + u ** 3 - c)
        u -= step
        if np.max(np.abs(step)) < 1e-15 * np.max(np.abs(u)):
            break
    return A, u, A + np.diag(3 * u ** 2)
