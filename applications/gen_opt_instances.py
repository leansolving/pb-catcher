# /// script
# requires-python = ">=3.10"
# ///
"""Generate OPB optimization instances for the P2b showcase theorems.

All objectives are written as `min:` (RoundingSat and cake_pb reject `max:`);
a maximization is written as `min:` with negated coefficients.

Variable numbering (1-based in OPB):
* Paley MIS / vertex cover: x{v+1} for vertex v (identical to IndependentSet.toOPB).
* Bin packing: x{i*m+j+1} = item i in bin j (identical to BinPacking.toOPB),
  y_j = x{n*m+j+1} = bin j used.
* Chromatic number: x{v*k+c+1} = vertex v has colour c, y_c = x{n*k+c+1} = colour c used.
"""
import sys
from pathlib import Path

APP = Path(__file__).resolve().parent


def paley_edges(p):
    qr = {(i * i) % p for i in range(1, p)}
    return [(u, v) for u in range(p) for v in range(u + 1, p) if (v - u) % p in qr]


def petersen_edges():
    e = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
    e += [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    return sorted(tuple(sorted(x)) for x in e)


def mycielski(n, edges):
    """Mycielski construction: vertices 0..n-1, copies n..2n-1, apex 2n."""
    e = list(edges)
    for (u, v) in edges:
        e.append((u, n + v))
        e.append((v, n + u))
    e += [(n + i, 2 * n) for i in range(n)]
    return 2 * n + 1, sorted(tuple(sorted(x)) for x in e)


def header(nv, nc):
    return f"* #variable= {nv} #constraint= {nc} #equal= 0 intsize= 6\n"


def mis_opb(n, edges):
    s = header(n, len(edges))
    s += "min: " + " ".join(f"-1 x{v+1}" for v in range(n)) + " ;\n"
    for (u, v) in edges:
        s += f"+1 ~x{u+1} +1 ~x{v+1} >= 1 ;\n"
    return s


def vc_opb(n, edges):
    s = header(n, len(edges))
    s += "min: " + " ".join(f"+1 x{v+1}" for v in range(n)) + " ;\n"
    for (u, v) in edges:
        s += f"+1 x{u+1} +1 x{v+1} >= 1 ;\n"
    return s


def binpack_opb(sizes, m, cap):
    """Item assignment clauses as in BinPacking.toOPB; capacity linked to y_j:
    sum_i s_i x_ij <= C y_j, written as sum_i s_i ~x_ij + C y_j >= total."""
    n, tot = len(sizes), sum(sizes)
    x = lambda i, j: i * m + j + 1
    y = lambda j: n * m + j + 1
    s = header(n * m + m, n + m)
    s += "min: " + " ".join(f"+1 x{y(j)}" for j in range(m)) + " ;\n"
    for i in range(n):
        s += " ".join(f"+1 x{x(i, j)}" for j in range(m)) + " >= 1 ;\n"
    for j in range(m):
        s += " ".join(f"+{sizes[i]} ~x{x(i, j)}" for i in range(n)) + f" +{cap} x{y(j)} >= {tot} ;\n"
    return s


def chrom_opb(n, edges, k):
    x = lambda v, c: v * k + c + 1
    y = lambda c: n * k + c + 1
    nc = n + len(edges) * k + n * k
    s = header(n * k + k, nc)
    s += "min: " + " ".join(f"+1 x{y(c)}" for c in range(k)) + " ;\n"
    for v in range(n):
        s += " ".join(f"+1 x{x(v, c)}" for c in range(k)) + " >= 1 ;\n"
    for (u, v) in edges:
        for c in range(k):
            s += f"+1 ~x{x(u, c)} +1 ~x{x(v, c)} >= 1 ;\n"
    for v in range(n):
        for c in range(k):
            s += f"+1 ~x{x(v, c)} +1 x{y(c)} >= 1 ;\n"
    return s


def write(path, text):
    path.write_text(text)
    print(path)


if __name__ == "__main__":
    for p in [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101]:
        write(APP / "paley_mis" / f"Paley_{p}_mis.opb", mis_opb(p, paley_edges(p)))
    for p in [13, 17, 29]:
        write(APP / "vcover" / f"Paley_{p}_vc.opb", vc_opb(p, paley_edges(p)))
    write(APP / "vcover" / "petersen_vc.opb", vc_opb(10, petersen_edges()))
    sizes = [10, 9, 8, 8, 6, 5, 4, 4, 4, 4, 4, 4]
    for m in [6, 7]:
        write(APP / "binpack" / f"bp12_m{m}_opt.opb", binpack_opb(sizes, m, 14))
    write(APP / "chromatic" / "petersen_k4.opb", chrom_opb(10, petersen_edges(), 4))
    n4, e4 = mycielski(5, [(i, (i + 1) % 5) for i in range(5)])  # Groetzsch graph
    write(APP / "chromatic" / "groetzsch_k5.opb", chrom_opb(n4, e4, 5))
    n5, e5 = mycielski(n4, e4)
    write(APP / "chromatic" / "mycielski5_k6.opb", chrom_opb(n5, e5, 6))
