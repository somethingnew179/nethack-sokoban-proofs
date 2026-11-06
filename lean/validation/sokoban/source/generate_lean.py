#!/usr/bin/env python3
"""Generate Maps.lean from independently audited canonical map declarations."""
from pathlib import Path
import argparse
import json
import extract

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2]
OUT = LEAN / 'NetHack/Sokoban/Maps.lean'


def list_nat(values):
    return '[' + ', '.join(map(str, values)) + ']'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = extract.data()
    assert json.loads((HERE / 'maps.json').read_text()) == data
    lines = ['/- Generated from all8 literal pinned NetHack Sokoban Lua variants.',
             'Canonical orientation; random objects/monsters are explicit profile exclusions.',
             'See validation/sokoban/source/{extract.py,generate_lean.py,lua_check.py}',
             'and docs/SOKOBAN_SOURCE_AUDIT_20261030_RU.md. -/',
             'import NetHack.Sokoban.Model', '', 'set_option maxRecDepth 10000',
             'set_option maxHeartbeats 2000000', '', 'namespace NetHack.Sokoban', '',
             'structure SourceMap where', '  id : String', '  sourceFile : String',
             '  sourceSHA256 : String', '  rows : List String', '  board : Board',
             '  initial : State', '  pits : List Nat', '  sourceHoles : List Nat',
             '  exitCell : Option Nat', '  doorStates : List (Nat × String)', '']
    names = []
    for m in data['maps']:
        name = m['id'].replace('-', '_')
        names.append(name)
        doors = [d['x'] + m['width'] * d['y'] for d in m['doors']]
        hazards = m['pitCells'] + m['holeCells']
        rows = ',\n    '.join(json.dumps(row) for row in m['rows'])
        exit = f"some {m['exitCell']}" if m['exitCell'] is not None else 'none'
        door_states = '[' + ', '.join(f'({cell}, {json.dumps(d["state"])})' for cell, d in zip(doors, m['doors'])) + ']'
        lines.extend([f'def {name} : SourceMap := {{', f'  id := {json.dumps(m["id"])}',
                      f'  sourceFile := {json.dumps(m["source"])}',
                      f'  sourceSHA256 := {json.dumps(m["source_sha256"])}',
                      '  rows := [\n    ' + rows + ']',
                      '  board := {', f'    width := {m["width"]}', f'    height := {m["height"]}',
                      f'    floor := {list_nat(m["floorCells"])}',
                      f'    rollingTraps := {list_nat(m["rollingCells"])}',
                      f'    doors := {list_nat(doors)}',
                      f'    exit := {m["exitCell"] or 0} }}',
                      '  initial := {', f'    player := {m["entryCell"]}',
                      f'    boulders := {list_nat(m["boulderCells"])}',
                      f'    holes := {list_nat(hazards)} }}',
                      f'  pits := {list_nat(m["pitCells"])}',
                      f'  sourceHoles := {list_nat(m["holeCells"])}',
                      f'  exitCell := {exit}', f'  doorStates := {door_states}', '}', '',
                      f'theorem {name}_initial_wellFormed : WellFormed {name}.board {name}.initial := by\n  simp only [WellFormed]\n  decide',
                      f'theorem {name}_initial_hazards : {name}.initial.holes.length = {len(hazards)} := by decide',
                      f'theorem {name}_initial_boulders : {name}.initial.boulders.length = {len(m["boulderCells"])} := by decide', ''])
    lines.extend(['def sourceMaps : List SourceMap := [' + ', '.join(names) + ']', '',
                  'theorem source_maps_count : sourceMaps.length = 8 := by decide', '',
                  'end NetHack.Sokoban', ''])
    text = '\n'.join(lines)
    if args.check:
        assert OUT.read_text() == text, 'Maps.lean differs from exact source generation'
        print('PASS generated Lean data for all8 source maps')
    else:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(text)
        print('Wrote', OUT)


if __name__ == '__main__':
    main()
