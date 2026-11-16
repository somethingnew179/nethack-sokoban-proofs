#!/usr/bin/env python3
"""Optimize credits on 18 PRE-EXISTING prescribed local footprints.

No boulder configurations are generated or searched. This diagnostic only
solves the small inequalities between those fixed words. The emitted numbers
are proposals; After265EastSix12 independently checks all real push cases.
"""
import ast
import hashlib
import json
import re
from diagnose import Model, HERE, REPO


def main():
    source = HERE/'Owner1007/After265EastFive12.lean'
    old = source.read_text()
    def rows(name):
        return ast.literal_eval(re.search(r'def '+name+r' : List [^\n]*? := (\[.*?\])\n',old).group(1))
    locks = rows('lockRows')[:14]+[[320,345],[320,319],[320,293],[]]
    board = Model('soko1_2')
    regions = rows('regionRows')[:14]+[
        sorted(board.floor-set(word)-({294} if index==2 else set()))
        for index,word in enumerate(locks[14:])]
    potential = REPO/'lean/NetHack/Sokoban/Generated/Soko12Potential.lean'
    debt = ast.literal_eval(re.search(r'def soko1_2Debt : List Nat := (\[[^\]]*\])',potential.read_text()).group(1))
    edges = []
    for phase,word in enumerate(locks):
        for cell in word:
            for direction,opposite in [('north','south'),('south','north'),('east','west'),('west','east')]:
                support = board.adjacent(cell,opposite)
                landing = board.adjacent(cell,direction)
                if support not in regions[phase] or support in word or landing not in board.floor or landing in board.doors or landing in word:
                    continue
                assert landing not in board.traps and landing not in board.initial[2]
                retained = {landing}|(set(word)-{cell})
                targets = [index for index,other in enumerate(locks)
                           if set(other)<=retained and cell in regions[index]]
                assert targets
                edges.append(dict(phase=phase,source=cell,direction=direction,landing=landing,
                                  price=1+debt[cell]-debt[landing],targets=targets))
    credits = [sum(debt[cell] for cell in word) for word in locks]
    for iteration in range(100):
        updated = [min([sum(debt[cell] for cell in word)]+[
            edge['price']+max(credits[index] for index in edge['targets'])
            for edge in edges if edge['phase']==phase]) for phase,word in enumerate(locks)]
        if updated==credits:
            break
        credits = updated
    else:
        raise AssertionError('Fixed local inequalities did not settle')
    assert credits==[6,7,8,6,8,5,5,5,0,4,5,6,5,4,2,3,4,0]
    report = dict(scope='Untrusted diagnostic on18 already prescribed local footprints; no global configuration search',
                  phase_count=18,new_boulder_configurations=0,credit_proposal=credits,
                  iterations=iteration,local_edges=edges,
                  source_sha256={str(path.relative_to(REPO)):hashlib.sha256(path.read_bytes()).hexdigest()
                                 for path in [source,potential]},
                  independent_checked_theorem='Owner1007.After265EastSix12.owned_credit')
    (HERE/'after265_manual_phase_credit_diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
    print('18 fixed words; new configurations=0; proposed credits=',credits)


if __name__=='__main__':
    main()
