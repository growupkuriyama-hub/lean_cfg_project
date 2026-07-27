#!/usr/bin/env python3
"""Exact folded NFA for odd-length generalized Fibonacci-root squares.

For L=2M+1, the two candidate four-summand types use root lengths
M+1, M, M-1, M-2:
    (1,1,1,1) and (2,1,1,0).
The M+1 group is the oversized generalized square group.  Its top root
column must be zero; it is tracked by one previous column count.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
import random

ODD_TYPES=((1,1,1,1),(2,1,1,0))
GroupState=tuple[tuple[int,...],tuple[int,...]]
# state=(oversized_prev (-1 initially), ordinary groups, lc,uc,mc)

@lru_cache(None)
def windows(T:int,k:int):
    if T==0:return ((),)
    return tuple(w for w in product(range(T+1),repeat=k+1)
                 if all(w[i]+w[i+1]<=T for i in range(k)))

def initial_states(counts):
    opts=[]
    for k,T in enumerate(counts[1:]):
        opts.append((((),()),) if T==0 else tuple((w[:k],w) for w in windows(T,k)))
    for mc in range(4):
        for groups in product(*opts):yield (-1,groups,0,mc,mc)

def ordinary_trans(T,k,state,q):
    if T==0:return [(0,0,((),()))]
    pref,seq=state
    if q is None or q>2*k:
        out=[]
        for x in range(T-seq[-1]+1):
            ns=(x,) if k==0 else seq[1:]+(x,)
            out.append((seq[0],seq[-1],(pref,ns)))
        return out
    if q==2*k:return [(seq[0],seq[-1],(pref,seq[1:]))]
    if k<=q<2*k:return [(seq[0],0,(pref,seq[1:]))]
    lo=pref[k-1-q]
    return [(lo,0,(((),()) if q==0 else (pref,())))]

def step_state(state,counts,q,sym):
    prev,groups,lc,uc,mc=state
    Tbig=counts[0]
    big=[]
    if prev<0:
        for x in range(Tbig+1):big.append((x,0,x))
    else:
        for x in range(Tbig-prev+1):big.append((x,prev,x))
    ops=[ordinary_trans(T,k,groups[k],q) for k,T in enumerate(counts[1:])]
    out=[]; lb=sym&1;ub=(sym>>1)&1
    for bc in big:
      for choices in product(*ops):
        lt=lc+bc[0]+sum(c[0] for c in choices)
        ut=uc+bc[1]+sum(c[1] for c in choices)
        if (lt&1)==lb and (ut&1)==ub:
          out.append((bc[2],tuple(c[2] for c in choices),lt>>1,ut>>1,mc))
    return out

def accepts(N,L,counts):
    if L%2==0 or N.bit_length()!=L:return False
    M=L//2;K=2;bits=[(N>>i)&1 for i in range(L)]
    S=set(initial_states(counts))
    for t in range(M):
        q=M-1-t; marker=q if q<=2*K else None
        sym=(bits[M+t]<<1)|bits[t]
        T=set()
        for s in S:T.update(step_state(s,counts,marker,sym))
        S=T
        if not S:return False
    return any(all(not p and not seq for p,seq in groups)
               and lc==mc and uc+prev==1
               for prev,groups,lc,uc,mc in S)

def roots(r):return [x for x in range(1<<r) if '11' not in format(x,f'0{r}b')]
def vals(r):return [x*((1<<r)+1) for x in roots(r)]
def direct(L,counts):
    M=L//2;lengths=[M+1,M,M-1,M-2];limit=1<<L;mask=(1<<limit)-1;r=1
    for rl,T in zip(lengths,counts):
      for _ in range(T):
        z=0
        for v in vals(rl):z|=r<<v
        r=z&mask
    return r

def main():
  rng=random.Random(20260727)
  for L in (11,13,15,17):
    for typ in ODD_TYPES:
      d=direct(L,typ)
      trials=(range(1<<(L-1),1<<L) if L<=13 else
              (rng.randrange(1<<(L-1),1<<L) for _ in range(200)))
      for N in trials:
        if bool((d>>N)&1)!=accepts(N,L,typ):raise AssertionError((L,typ,N))
      print('PASS',L,typ)
if __name__=='__main__':main()


def accepts_even_frame(number: int, bit_length: int, counts) -> bool:
    """Use the odd folded frame with a zero top bit for an even-length input."""
    if bit_length % 2 or number.bit_length() != bit_length:
        return False
    half = bit_length // 2
    bits = [(number >> i) & 1 for i in range(bit_length)] + [0]
    states = set(initial_states(counts))
    for position in range(half):
        remaining = half - 1 - position
        marker = remaining if remaining <= 4 else None
        symbol = (bits[half + position] << 1) | bits[position]
        successors = set()
        for state in states:
            successors.update(step_state(state, counts, marker, symbol))
        states = successors
        if not states:
            return False
    return any(
        all(not prefix and not sequence for prefix, sequence in groups)
        and lower_carry == middle_carry
        and upper_carry + previous == 0
        for previous, groups, lower_carry, upper_carry, middle_carry in states
    )


def run_all_regression_tests() -> None:
    """Run compact independent odd/even folded-NFA regression checks."""
    rng = random.Random(20260727)

    for bit_length in (11,):
        for counts in ODD_TYPES:
            expected = direct(bit_length, counts)
            for number in range(1 << (bit_length - 1), 1 << bit_length):
                observed = accepts(number, bit_length, counts)
                if bool((expected >> number) & 1) != observed:
                    raise AssertionError(('odd', bit_length, counts, number))
            print('PASS odd exhaustive', bit_length, counts)

    for bit_length in (13, 15, 17):
        for counts in ODD_TYPES:
            expected = direct(bit_length, counts)
            for _ in range(100):
                number = rng.randrange(1 << (bit_length - 1), 1 << bit_length)
                observed = accepts(number, bit_length, counts)
                if bool((expected >> number) & 1) != observed:
                    raise AssertionError(('odd', bit_length, counts, number))
            print('PASS odd random', bit_length, counts)

    for bit_length in (10,):
        for counts in ODD_TYPES:
            expected = direct(bit_length + 1, counts)
            for number in range(1 << (bit_length - 1), 1 << bit_length):
                observed = accepts_even_frame(number, bit_length, counts)
                if bool((expected >> number) & 1) != observed:
                    raise AssertionError(('even', bit_length, counts, number))
            print('PASS even exhaustive', bit_length, counts)

    for bit_length in (12, 14, 16, 18):
        for counts in ODD_TYPES:
            expected = direct(bit_length + 1, counts)
            for _ in range(100):
                number = rng.randrange(1 << (bit_length - 1), 1 << bit_length)
                observed = accepts_even_frame(number, bit_length, counts)
                if bool((expected >> number) & 1) != observed:
                    raise AssertionError(('even', bit_length, counts, number))
            print('PASS even random', bit_length, counts)

