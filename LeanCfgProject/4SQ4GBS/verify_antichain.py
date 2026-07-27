#!/usr/bin/env python3
from __future__ import annotations
import argparse, sys, time, os
from dataclasses import dataclass
import numpy as np
from numba import njit, prange, set_num_threads

@dataclass
class Graph:
    header: str
    sizes: list[int]
    initial: np.ndarray
    accept: np.ndarray
    interior: list
    tail: list

def bits_from_ids(n, ids):
    a=np.zeros((n+63)//64,dtype=np.uint64)
    for x in ids: a[x>>6] |= np.uint64(1)<<np.uint64(x&63)
    return a

def parse_row(line):
    out=[]
    for f in line.rstrip('\n').split('|'):
        out.append([] if f in ('','-') else [int(x) for x in f.split(',')])
    return out

def load(path):
    with open(path) as f:
        header=f.readline().strip()
        p=f.readline().split(); sizes=list(map(int,p[1:]))
        line=f.readline().rstrip('\n'); initial=bits_from_ids(sizes[0],map(int,line.split()[1:]))
        line=f.readline().rstrip('\n'); accept=bits_from_ids(sizes[5],map(int,line.split()[1:]))
        assert f.readline().strip()=='TRANS INTERIOR'
        interior=[parse_row(f.readline()) for _ in range(sizes[0])]
        tail=[]
        for phase in range(5):
            f.readline(); tail.append([parse_row(f.readline()) for _ in range(sizes[phase])])
    return Graph(header,sizes,initial,accept,interior,tail)

def to_csr(rows):
    pred_n=len(rows)
    offsets=np.zeros((4,pred_n+1),dtype=np.int64)
    flats=[]
    for sym in range(4):
        vals=[]
        for s,row in enumerate(rows):
            vals.extend(row[sym]); offsets[sym,s+1]=len(vals)
        flats.append(np.asarray(vals,dtype=np.int32))
    return offsets,flats

@njit(cache=True)
def popcount64(x):
    c=0
    while x:
        x &= x-np.uint64(1); c+=1
    return c

@njit(cache=True, parallel=True)
def generate_candidates(A, syms, offsets, f0, f1, f2, f3, pred_n):
    m=A.shape[0]; words=(pred_n+63)//64
    out=np.zeros((m*len(syms),words),dtype=np.uint64)
    flats=(f0,f1,f2,f3)
    for z in prange(m*len(syms)):
        i=z//len(syms); sym=syms[z%len(syms)]; flat=flats[sym]
        for s in range(pred_n):
            hit=False
            for e in range(offsets[sym,s],offsets[sym,s+1]):
                t=flat[e]
                if (A[i,t>>6] >> np.uint64(t&63)) & np.uint64(1):
                    hit=True; break
            if hit: out[z,s>>6] |= np.uint64(1)<<np.uint64(s&63)
    return out

@njit(cache=True)
def row_popcounts(X):
    out=np.empty(X.shape[0],dtype=np.int32)
    for i in range(X.shape[0]):
        c=0
        for j in range(X.shape[1]): c += popcount64(X[i,j])
        out[i]=c
    return out

@njit(cache=True)
def subset_row(K,S):
    for j in range(K.shape[0]):
        if K[j] & ~S[j]: return False
    return True

@njit(cache=True)
def minimalize_sorted(X, universe):
    n,words=X.shape
    keep=np.zeros((n,words),dtype=np.uint64)
    heads=np.full(universe,-1,dtype=np.int32)
    nxt=np.full(n,-1,dtype=np.int32)
    kc=0
    for ii in range(n):
        S=X[ii]
        empty=True
        for w in range(words):
            if S[w]: empty=False; break
        if empty:
            keep[0,:]=S; return keep[:1]
        dominated=False
        first=-1
        # Iterate all bits in S, exactly as the C++ bucket method.
        for wi in range(words):
            x=S[wi]
            while x:
                low=x & (np.uint64(0)-x)
                b=wi*64
                y=low
                while y>>np.uint64(1):
                    y >>= np.uint64(1); b+=1
                if first<0: first=b
                idx=heads[b]
                while idx!=-1:
                    if subset_row(keep[idx],S):
                        dominated=True; break
                    idx=nxt[idx]
                if dominated: break
                x &= x-np.uint64(1)
            if dominated: break
        if not dominated:
            keep[kc,:]=S
            nxt[kc]=heads[first]; heads[first]=kc; kc+=1
    return keep[:kc].copy()

def minimalize(X,universe):
    pcs=row_popcounts(X)
    order=np.argsort(pcs,kind='stable')
    return minimalize_sorted(X[order],universe)

def bitset_disjoint_rows(A,b):
    return np.any(np.all((A & b)==0,axis=1))
def same_family(A,B):
    if A.shape!=B.shape:return False
    # Convert rows to bytes for exact unordered comparison.
    return {row.tobytes() for row in A}=={row.tobytes() for row in B}
def stats(tag,A):
    pcs=row_popcounts(A)
    print(f'{tag} sets={len(A)} min={pcs.min()} max={pcs.max()} avg={int(pcs.sum()//len(A))}',file=sys.stderr,flush=True)

def verify(g):
    csr_int=to_csr(g.interior); csr_tail=[to_csr(x) for x in g.tail]
    A=g.accept.reshape(1,-1)
    print('sizes',' '.join(map(str,g.sizes)),f'init={row_popcounts(g.initial.reshape(1,-1))[0]} accept={row_popcounts(A)[0]}',file=sys.stderr,flush=True)
    even=g.header.startswith('EVEN_')
    for p in range(4,-1,-1):
        syms=np.array([2,3] if even and p==4 else [0,1,2,3],dtype=np.int32)
        off,fl=csr_tail[p]
        A=minimalize(generate_candidates(A,syms,off,*fl,g.sizes[p]),g.sizes[p]); stats(f'tail p={p}',A)
    syms=np.array([0,1,2,3],dtype=np.int32); off,fl=csr_int
    for depth in (1,2):
        A=minimalize(generate_candidates(A,syms,off,*fl,g.sizes[0]),g.sizes[0]); stats(f'depth={depth}',A)
        if bitset_disjoint_rows(A,g.initial): return False,f'COUNTEREXAMPLE EXISTS AT DEPTH {depth}'
    for it in range(1,101):
        P=generate_candidates(A,syms,off,*fl,g.sizes[0])
        B=minimalize(np.vstack((A,P)),g.sizes[0]); stats(f'closure={it}',B)
        if bitset_disjoint_rows(B,g.initial):return False,f'COUNTEREXAMPLE EXISTS IN CLOSURE ITER {it}'
        if same_family(A,B):
            return True,('PROVED EVEN VIA ODD FRAME: all even L>=14 are covered by the two four-summand types.' if even else 'PROVED ODD INCLUSION: all odd L>=15 are covered by the two four-summand types.')
        A=B
    return False,'ABORT no fixed point'

def main():
    ap = argparse.ArgumentParser(
        description='Verify backward-antichain certificates using Python/Numba.'
    )
    ap.add_argument(
        'graphs', nargs='*',
        help='Graph certificate files. With no arguments, verify odd_graph.txt and even_graph.txt next to this script.'
    )
    ap.add_argument('--threads', type=int, default=min(4, os.cpu_count() or 1))
    args = ap.parse_args()
    set_num_threads(max(1, args.threads))
    base = os.path.dirname(os.path.abspath(__file__))
    paths = args.graphs or [
        os.path.join(base, 'odd_graph.txt'),
        os.path.join(base, 'even_graph.txt'),
    ]
    all_ok = True
    for path in paths:
        t = time.perf_counter()
        graph = load(path)
        ok, message = verify(graph)
        print(message)
        print(
            f'{os.path.basename(path)} elapsed_seconds={time.perf_counter()-t:.3f}',
            file=sys.stderr,
        )
        all_ok = all_ok and ok
    raise SystemExit(0 if all_ok else 1)

if __name__ == '__main__':
    main()
