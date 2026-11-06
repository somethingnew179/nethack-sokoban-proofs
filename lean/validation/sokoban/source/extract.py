#!/usr/bin/env python3
"""Extract the fixed Sokoban geometry/declarations from pinned NetHack Lua.

Only literal map/boulder/trap/stair/door/branch declarations are puzzle data.
All other source calls are retained as boundary metadata, never interpreted as
absent gameplay. `--check` independently re-extracts and compares the JSON.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2]
ROOT = LEAN.parent
PIN = 'b0c09c878e1f9f62bc7ab20e6edafd6108c325a0'
OUT = HERE / 'maps.json'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract(path: Path) -> dict:
    text = path.read_text()
    blocks = list(re.finditer(r'des\.map\(\[\[\n(.*?)\n\]\]\)', text, re.S))
    assert len(blocks) == 1, path
    # Lua long-string wall runs contain "--" and are not comments.
    active = re.sub(r'--[^\n]*', '', text[:blocks[0].start()] + 'des.map()' + text[blocks[0].end():])
    rows = blocks[0].group(1).splitlines()
    width = max(map(len, rows))
    height = len(rows)
    rows = [row.ljust(width) for row in rows]
    assert set(''.join(rows)) <= set(' .|-+'), path
    floor = [[x, y] for y, row in enumerate(rows) for x, c in enumerate(row) if c == '.']
    doors_on_map = {(x, y) for y, row in enumerate(rows) for x, c in enumerate(row) if c == '+'}
    boulders = [[int(x), int(y)] for x, y in re.findall(r'des\.object\(\s*"boulder"\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', active)]
    assert len(boulders) == len(re.findall(r'des\.object\(\s*"boulder"', active)), (path, boulders)
    traps = [{'kind': kind, 'x': int(x), 'y': int(y)} for kind, x, y in re.findall(r'des\.trap\(\s*"([^"]+)"\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', active)]
    assert len(traps) == active.count('des.trap('), path
    assert {t['kind'] for t in traps} <= {'pit', 'hole', 'rolling boulder'}, path
    stairs = [{'direction': direction, 'x': int(x), 'y': int(y)} for direction, x, y in re.findall(r'des\.stair\(\s*"(up|down)"\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', active)]
    assert len(stairs) == active.count('des.stair('), path
    doors = [{'state': state, 'x': int(x), 'y': int(y)} for state, x, y in re.findall(r'des\.door\(\s*"([^"]+)"\s*,\s*(\d+)\s*,\s*(\d+)\s*\)', active)]
    assert {(d['x'], d['y']) for d in doors} == doors_on_map, path
    branches = re.findall(r'des\.levregion\(\{\s*region\s*=\s*\{\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\}\s*,\s*type\s*=\s*"branch"\s*\}\)', active)
    assert len(branches) == active.count('des.levregion('), path
    entry = None
    if branches:
        assert len(branches) == 1
        x, y, x2, y2 = map(int, branches[0])
        assert (x, y) == (x2, y2)
        entry = [x, y]
    else:
        down = [s for s in stairs if s['direction'] == 'down']
        assert len(down) == 1
        entry = [down[0]['x'], down[0]['y']]
    up = [s for s in stairs if s['direction'] == 'up']
    exit = [up[0]['x'], up[0]['y']] if up else None
    for x, y in [*boulders, *[[t['x'], t['y']] for t in traps], entry, *[[s['x'], s['y']] for s in stairs]]:
        assert [x, y] in floor, (path, x, y)
    assert len({tuple(p) for p in boulders}) == len(boulders)
    assert not ({tuple(p) for p in boulders} & {(t['x'], t['y']) for t in traps})
    flags = re.search(r'des\.level_flags\(([^)]*)\)', active)[1]
    flags = re.findall(r'"([^"]+)"', flags)
    def coords(kind):
        return [[t['x'], t['y']] for t in traps if t['kind'] == kind]
    def cells(points):
        return [x + width * y for x, y in points]
    calls = sorted(set(re.findall(r'\bdes\.(\w+)\s*\(', active)))
    return {
        'id': path.stem, 'source': str(path.relative_to(ROOT)), 'source_sha256': sha(path),
        'width': width, 'height': height, 'rows': rows,
        'floor': floor, 'floorCells': cells(floor),
        'boulders': boulders, 'boulderCells': cells(boulders),
        'pits': coords('pit'), 'pitCells': cells(coords('pit')),
        'holes': coords('hole'), 'holeCells': cells(coords('hole')),
        'rollingTraps': coords('rolling boulder'), 'rollingCells': cells(coords('rolling boulder')),
        'stairs': stairs, 'branchEntry': entry if branches else None,
        'entry': entry, 'entryCell': cells([entry])[0],
        'exit': exit, 'exitCell': cells([exit])[0] if exit else None,
        'doors': doors, 'levelFlags': flags,
        'allSourceDesCalls': calls,
        'generationBoundary': {
            'orientation': 'canonical literal map, before optional horizontal/vertical level flip',
            'floorProfile': 'literal dots; all authored closed/locked door cells excluded',
            'entry': 'branch singleton on soko4; downstairs on soko1..3',
            'extraRollingAmmo': False,
            'extraRollingAmmoSource': 'src/trap.c find_random_launch_coord returns FALSE if Sokoban; mkroll_launch sets both launch endpoints to the trap and creates no ammo',
            'randomObjectsAndMonsters': 'present in original, excluded only by explicit pure puzzle profile',
            'goal': 'all original PIT/HOLE traps removed; stairs/reward retrieval is separate',
        },
    }


def data():
    paths = sorted((ROOT / 'dat').glob('soko[1-4]-[12].lua'))
    assert len(paths) == 8
    return {'schema': 'nethack-sokoban-source-v1', 'source_commit': PIN,
            'coordinates': 'zero-based map-relative; cell=x+width*y; rows retain trailing spaces',
            'maps': [extract(path) for path in paths]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = data()
    encoded = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.check:
        assert OUT.read_text() == encoded, 'maps.json differs from pinned literal sources'
        print('PASS all8 exact literal maps, declarations, coordinates and source hashes')
    else:
        OUT.write_text(encoded)
        print('Wrote', OUT)
    for m in result['maps']:
        print(m['id'], f"{m['width']}x{m['height']}", 'floor', len(m['floor']), 'boulders', len(m['boulders']), 'pits/holes', len(m['pits']) + len(m['holes']), 'rolling', len(m['rollingTraps']), 'entry', m['entry'])


if __name__ == '__main__':
    main()
