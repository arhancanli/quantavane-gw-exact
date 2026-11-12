#!/usr/bin/env python3
"""Write GwExact/Cert.lean from CaDiCaL's LRAT refutation of the GW CNF (n, R, k, l) = (53, 5, 3, 4).

The CNF is the one of gw_cnf.py (Quantavane, 11 Nov 2026): atom i*R + c (DIMACS i*R + c + 1) says
that point i + 1 has colour c; clause families, in order: per point "at least one colour" and
"not both a < b"; per first point a and difference d: "not all of a, a + d, ..., a + (l-1)d have
colour c" and "not (c0, c1, c2) on a, a + d, a + 2d" for distinct colours; the unit "point 1 has
colour 0"; the first-occurrence order clauses. This script rebuilds the CNF in that order, checks
its SHA-256 against the one the LRAT proof refutes, and gives every original clause a descriptor
(kind and parameters) from which GwExact.descCls recomputes the clause in Lean.

Nothing here is trusted by the Lean proof: a wrong descriptor or a wrong step makes the kernel
check fail; it cannot make it succeed.

Step encoding (one Nat per derived clause, least significant bits first):
  nl (8 bits) | nl literals, 10 bits each (2 * atom + 1 if positive) |
  nh (8 bits) | nh hints of 44 bits each.
Hint: bit 0 = 1: an earlier derived clause, bits 1.. its index (0-based, in proof order);
      bit 0 = 0: an original clause, bits 1.. its descriptor:
      kind (3 bits) | f1 | f2 | f3 | f4 | f5 (8 bits each).
Kinds: 0 at least one colour at position f1; 1 not both colours f2 < f3 at position f1;
2 not all of f1 + j*f2 (j < l) have colour f3; 3 not colours (f3, f4, f5) on f1, f1 + f2,
f1 + 2*f2; 4 position 0 has colour 0; 5 colour f2 at position f1 needs colour f2 - 1 before f1.

Usage: make_cert.py PROOF.lrat OUT.lean
"""
import hashlib, itertools, sys

N, R, K, L = 53, 5, 3, 4
CNF_SHA256 = 'ff0402355858a7074c8893681205c9fa1a20aea2f254cfb695e2211fdbc12072'
LRAT_SHA256 = 'e0191268456191ba2f3cf7fe7e6b52c04923e234134fa87eb8a7e68b67760db1'


def v(i, c):
    return i * R + c + 1


def desc(kind, *f):
    code = kind
    for j, x in enumerate(f):
        assert 0 <= x < 256
        code |= x << (3 + 8 * j)
    return code


def clauses():
    out = []
    for i in range(N):
        out.append(([v(i, c) for c in range(R)], desc(0, i)))
        for a, b in itertools.combinations(range(R), 2):
            out.append(([-v(i, a), -v(i, b)], desc(1, i, a, b)))
    for a in range(N):
        for d in range(1, N):
            if a + (L - 1) * d < N:
                for c in range(R):
                    out.append(([-v(a + j * d, c) for j in range(L)], desc(2, a, d, c)))
            if a + (K - 1) * d < N and K <= R:
                pts = [a + j * d for j in range(K)]
                for cols in itertools.permutations(range(R), K):
                    out.append(([-v(p, cc) for p, cc in zip(pts, cols)], desc(3, a, d, *cols)))
    out.append(([v(0, 0)], desc(4)))
    for i in range(1, N):
        for c in range(1, R):
            out.append(([-v(i, c)] + [v(j, c - 1) for j in range(i)], desc(5, i, c)))
    return out


def lean_clause(code):
    """The clause GwExact.descCls computes from a descriptor (as a set of DIMACS literals)."""
    kind = code & 7
    f = [(code >> (3 + 8 * j)) & 255 for j in range(5)]
    if kind == 0:
        return {v(f[0], c) for c in range(R)}
    if kind == 1:
        return {-v(f[0], f[1]), -v(f[0], f[2])}
    if kind == 2:
        return {-v(f[0] + j * f[1], f[2]) for j in range(L)}
    if kind == 3:
        return {-v(f[0], f[2]), -v(f[0] + f[1], f[3]), -v(f[0] + 2 * f[1], f[4])}
    if kind == 4:
        return {v(0, 0)}
    if kind == 5:
        return {-v(f[0], f[1])} | {v(j, f[1] - 1) for j in range(f[0])}
    raise ValueError(kind)


def main():
    proof, out = sys.argv[1], sys.argv[2]
    data = open(proof, 'rb').read()
    assert hashlib.sha256(data).hexdigest() == LRAT_SHA256, 'unexpected LRAT file'
    cls = clauses()
    dimacs = f'p cnf {N * R} {len(cls)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c, _ in cls)
    assert hashlib.sha256(dimacs.encode()).hexdigest() == CNF_SHA256, 'CNF differs from gw_cnf.py'
    for c, code in cls:
        assert set(c) == lean_clause(code), (c, code)
    m = len(cls)
    steps, index, kinds = [], {}, [0] * 7
    for line in data.decode().splitlines():
        t = line.split()
        if not t or t[1] == 'd':
            continue
        cid = int(t[0])
        assert cid == m + 1 + len(steps), 'ids must be dense'
        i = 1
        lits = []
        while t[i] != '0':
            lits.append(int(t[i]))
            i += 1
        hints = [int(x) for x in t[i + 1:-1]]
        code, pos = 0, 0

        def put(x, w):
            nonlocal code, pos
            assert 0 <= x < (1 << w)
            code |= x << pos
            pos += w
        put(len(lits), 8)
        for x in lits:
            put(2 * (abs(x) - 1) + (1 if x > 0 else 0), 10)
        put(len(hints), 8)
        for h in hints:
            assert h > 0, 'RUP hints only'
            if h <= m:
                d = cls[h - 1][1]
                kinds[d & 7] += 1
                put(d << 1, 44)
            else:
                kinds[6] += 1
                put((index[h] << 1) | 1, 44)
        index[cid] = len(steps)
        steps.append(code)
    assert not lits, 'the last step must be the empty clause'
    with open(out, 'w') as f:
        f.write('module\n\n@[expose] public section\n\n')
        f.write('/-!\n# The certificate: an LRAT refutation of the GW CNF for `[1, 53]`, five colours, `l = 4`\n\n')
        f.write('Generated by `scripts/make_cert.py` from CaDiCaL 3.0.1\'s trimmed LRAT proof (SHA-256\n')
        f.write(f'`{LRAT_SHA256}`) of the CNF of\n')
        f.write(f'Quantavane\'s `gw_cnf.py 53 5 3 4` (SHA-256 `{CNF_SHA256}`).\n')
        f.write(f'{len(steps)} derived clauses; the last is the empty clause. The encoding is described in\n')
        f.write('`GwExact.Check` and in the script. This is untrusted data: `GwExact.checkCert_sound` holds for\n')
        f.write('every list of natural numbers.\n-/\n\nnamespace GwExact\n\n')
        f.write('/-- The derived clauses of the refutation, one natural number per clause. -/\n')
        f.write('def cert : List Nat := [\n')
        f.write(',\n'.join(hex(s) for s in steps))
        f.write(']\n\nend GwExact\n')
    print(f'{len(steps)} steps, {m} original clauses; hints by kind (0..5, derived):', kinds)


if __name__ == '__main__':
    main()
