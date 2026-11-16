#!/usr/bin/env python3
"""Ten explicit two-token phases; static walking components, no state search."""
from collections import deque
import json
from diagnose import HERE, Model, DIRS

PHASES = [([318,371],396),([318,345],371),([318,319],345),([318,293],319),
          ([318,292],293),([318,291],292),([319,345],318),([319,293],318),
          ([319,292],318),([292,293],319)]

def main():
    model=Model('soko1_2')
    rows=[]
    for locks,hero in PHASES:
        occupied=set(locks)
        seen={hero}
        queue=deque([hero])
        while queue:
            cell=queue.popleft()
            for direction,(dx,dy) in DIRS.items():
                target=model.adjacent(cell,direction)
                if target not in model.floor or target in model.doors or target in occupied:
                    continue
                if dx and dy:
                    sides=[model.adjacent(cell,'east' if dx>0 else 'west'),
                           model.adjacent(cell,'south' if dy>0 else 'north')]
                    if all(side not in model.floor or side in occupied for side in sides):
                        continue
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
        rows.append(dict(locks=locks,seed=hero,region=sorted(seen)))
    artifact=dict(scope='Ten manually specified pair phases; BFS over walking cells only, all holes ignored conservatively',phases=rows)
    (HERE/'bottom2_phases12.json').write_text(json.dumps(artifact,indent=2)+'\n')
    print('Recreated ten fixed-pair walking components; closure/price must be checked by Lean')

if __name__=='__main__':
    main()
