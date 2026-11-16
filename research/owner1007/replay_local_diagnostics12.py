#!/usr/bin/env python3
"""Two fixed local Sokoban diagnostics; no boulder-configuration search.

The UP case starts from an explicitly relaxed six-stone state and leaves
12 holes. It is a counterexample to an isolated-UP price hypothesis.
The original-map case checks one 31-push prefix and six local support probes.
Neither case is an original winning witness.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import sys

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    diagnostic_source = repo / "research/owner1007/diagnose.py"
    sys.path.insert(0, str(diagnostic_source.parent))
    from diagnose import Model

    model = Model("soko1_2")
    potential_source = repo / "lean/NetHack/Sokoban/Generated/Soko12Potential.lean"
    potential_text = potential_source.read_text()
    debt = ast.literal_eval(re.search(r"def soko1_2Debt : List Nat := (\[[^\]]*\])", potential_text).group(1))
    credit = ast.literal_eval(re.search(r"def soko1_2Credit : List Nat := (\[[^\]]*\])", potential_text).group(1))

    upper_start = (187, frozenset([108,158,159,161,186,212]), model.initial[2])
    upper_commands = [(186,"west")]
    upper_commands += [(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    upper_commands += [(212,"north"),(186,"north"),(160,"north"),(134,"north"),(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    upper_commands += [(185,"east"),(186,"north"),(160,"north"),(134,"north"),(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    upper_commands += [(158,"north"),(132,"east"),(133,"east"),(134,"north"),(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    upper_commands += [(159,"north"),(133,"east"),(134,"north"),(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    upper_commands += [(161,"south"),(187,"south"),(213,"west"),(212,"north"),(186,"north"),(160,"north"),(134,"north"),(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    upper_result = model.macros(upper_start, upper_commands)
    assert upper_result is not None
    upper_final, upper_path = upper_result
    consumed_credit = sum(credit[c] for c in upper_start[2] - upper_final[2])
    upper_energy = sum(debt[c] for c in upper_start[1]) + len(upper_commands) - consumed_credit
    assert len(upper_commands) == 47 and len(upper_path) == 114
    assert upper_final[1] == frozenset() and len(upper_final[2]) == 12 and upper_energy == 2

    north_commands = [(371,"north"),(345,"north"),(319,"north"),(293,"west"),(292,"west"),(291,"west"),
        (193,"north"),(192,"west"),(191,"west"),(190,"west"),(265,"north"),(263,"west"),
        (213,"west"),(212,"west"),(187,"north"),(186,"north"),(238,"south"),(158,"north"),(132,"south"),
        (108,"north"),(82,"north"),(56,"north"),(30,"east"),(161,"south"),(187,"south"),
        (160,"north"),(134,"north"),(108,"north"),(82,"north"),(56,"north"),(30,"east")]
    north_result = model.macros(model.initial, north_commands)
    assert north_result is not None
    north_final, north_path = north_result
    walks = model.walks(north_final)
    opposite = dict(north="south", south="north", east="west", west="east")
    probes = []
    for source, direction in [(213,"north"),(213,"west"),(213,"east"),(239,"north"),(239,"south"),(264,"north")]:
        support = model.adjacent(source, opposite[direction])
        probes.append(dict(source=source, direction=direction, support=support,
            support_reachable=support in walks,
            prescribed_push_enabled=model.macros(north_final, [(source,direction)]) is not None))
    assert len(north_commands) == 31 and len(north_final[2]) == 16
    assert [p["prescribed_push_enabled"] for p in probes] == [False,False,True,False,False,False]

    def state_json(state):
        return dict(player=state[0], boulders=sorted(state[1]), holes=sorted(state[2]))
    sources = [
        Path(__file__).resolve(),
        diagnostic_source,
        repo / "lean/NetHack/Sokoban/Model.lean",
        repo / "lean/NetHack/Sokoban/Maps.lean",
        potential_source,
    ]
    report = dict(
        task="nethack-invariants-codex-owner1007",
        method="Two explicitly prescribed push lists. BFS is used only to walk to each prescribed support; there is no puzzle-state search.",
        validation_kind="bounded Python diagnostic replay; kernel certificates are separate Lean files",
        source_sha256={str(p): sha(p) for p in sources},
        cases=[
            dict(id="isolated_UP6_counterexample", canonical_initial=False,
                purpose="Refutes the isolated all-consumed-UP6 future-energy-at-least-4 hypothesis; it does not refute an original-map lower bound.",
                initial=state_json(upper_start), commands=upper_commands, path=upper_path,
                legal=True, pushes=len(upper_commands), moves=len(upper_path),
                final=state_json(upper_final), all_six_stones_consumed=True,
                original_goal=False, remaining_holes=12, owned_energy=upper_energy,
                owned_energy_identity=dict(initial_debt=sum(debt[c] for c in upper_start[1]),
                    pushes=47, consumption_credit=consumed_credit),
                kernel_scope="A separate Lean trace uses this same custom six-stone start and unchanged Model; it is not a canonical winning witness."),
            dict(id="original_North_failed_31_push_plan", canonical_initial=True,
                purpose="Refutes one specific North upper-plan continuation, not all North strategies.",
                initial=state_json(model.initial), commands=north_commands, path=north_path,
                legal_prefix=True, pushes=len(north_commands), moves=len(north_path),
                final=state_json(north_final), original_goal=False,
                remaining_holes=len(north_final[2]), reachable_component=sorted(walks), probes=probes),
        ])
    rendered = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(rendered)
        print(json.dumps(dict(output=str(args.output), sha256=sha(args.output),
            UP6=dict(pushes=47,moves=114,energy=2,remaining_holes=12),
            original_North=dict(pushes=31,moves=len(north_path),remaining_holes=16))))
    else:
        print(rendered, end="")

if __name__ == "__main__":
    main()
