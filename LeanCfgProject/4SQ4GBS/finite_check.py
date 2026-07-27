#!/usr/bin/env python3
"""Finite verification for generalized Fibonacci-root binary squares.

A designated-length root w may begin with zero, but it must avoid the factor 11.
The corresponding generalized binary square is val_2(ww).

The program verifies finite Waring data and the fixed length-type families that
motivate the conjectural four-square theorem.
"""
from __future__ import annotations
import argparse
from functools import lru_cache

ODD_TYPES = ((1,1,1,1),(2,1,1,0))
# root lengths M+1, M, M-1, M-2 for an L=2M+1 bit input
EVEN_TYPES = ((2,1,1,0),(1,2,0,1),(2,1,0,1),(2,0,2,0),(2,0,1,1))
# root lengths M, M-1, M-2, M-3 for an L=2M bit input

@lru_cache(maxsize=None)
def roots_no11(r:int)->tuple[int,...]:
    return tuple(x for x in range(1<<r) if '11' not in format(x,f'0{r}b'))

def squares_of_length(r:int)->tuple[int,...]:
    return tuple(x*((1<<r)+1) for x in roots_no11(r))

def all_squares_below(limit:int)->list[int]:
    vals={0}
    max_r=(limit.bit_length()+1)//2+1
    for r in range(1,max_r+1):
        vals.update(v for v in squares_of_length(r) if v<limit)
    return sorted(vals)

def next_sumset(reachable:int, vals:list[int], limit:int)->int:
    mask=(1<<limit)-1
    out=0
    for v in vals: out |= reachable<<v
    return out & mask

def exceptions(reachable:int,limit:int)->tuple[int,int,list[int]]:
    e=((1<<limit)-1)^reachable
    first=[];x=e
    while x and len(first)<100:
        b=x&-x;first.append(b.bit_length()-1);x-=b
    return e.bit_count(),(e.bit_length()-1 if e else -1),first

def type_sumset(L:int,counts:tuple[int,...],odd:bool)->int:
    M=L//2;limit=1<<L;mask=(1<<limit)-1;r=1
    lengths=([M+1,M,M-1,M-2] if odd else [M,M-1,M-2,M-3])
    for root_len,t in zip(lengths,counts):
        vals=squares_of_length(root_len)
        for _ in range(t):
            out=0
            for v in vals: out |= r<<v
            r=out&mask
    return r

def type_coverage(L:int)->tuple[int,int]:
    odd=L%2==1;types=ODD_TYPES if odd else EVEN_TYPES
    u=0
    for typ in types:u|=type_sumset(L,typ,odd)
    lo=1<<(L-1);mask=(1<<lo)-1
    missing=mask^((u>>lo)&mask)
    return missing.bit_count(),(lo+missing.bit_length()-1 if missing else -1)

def main()->None:
    ap=argparse.ArgumentParser();ap.add_argument('--bits',type=int,default=24)
    args=ap.parse_args();B=args.bits
    if not 8<=B<=26: raise SystemExit('--bits must be between 8 and 26')
    limit=1<<B;vals=all_squares_below(limit)
    print(f'generalized Fibonacci-root squares below 2^{B}: {len(vals)}')
    r=1
    for h in range(1,5):
        r=next_sumset(r,vals,limit)
        count,largest,first=exceptions(r,limit)
        print(f'at most {h} summands: exceptions={count}, largest={largest}')
        if h==4: print('four-summand exceptions:',first)
    print('fixed length-type coverage:')
    for L in range(15,B+1):
        missing,largest=type_coverage(L)
        print(f'  L={L}: '+('covered' if missing==0 else f'{missing} missing; largest={largest}'))

if __name__=='__main__':main()
