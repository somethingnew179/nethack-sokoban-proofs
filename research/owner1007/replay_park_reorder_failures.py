#!/usr/bin/env python3
"""Two prescribed canonical schedule variants; no boulder-state search.

Both are expected failures, not upper witnesses or lower bounds. Only the
walking connection to each prescribed push uses fixed-boulder BFS.
"""
import hashlib
import json
from pathlib import Path
from diagnose import Model, HERE, REPO, witness, replay


def first_failure(model, commands):
    state = model.initial
    for index, command in enumerate(commands):
        result = model.macros(state, [command])
        if result is None:
            source, direction = command
            opposite = dict(north="south", south="north", east="west", west="east")
            support = model.adjacent(source, opposite[direction])
            return dict(successful_prefix_pushes=index, failed_command=command,
                        player=state[0], support=support,
                        support_reachable=support in model.walks(state),
                        boulders=sorted(state[1]), holes=sorted(state[2]))
        state = result[0]
    raise AssertionError("Expected this prescribed candidate to fail")


def main():
    original11 = json.loads((HERE / "witness11_342.json").read_text())["events"]
    commands11 = [(event["source"], event["direction"])
                  for event in original11 if event["identity"] != 321]
    failure11 = first_failure(Model("soko1_1"), commands11)
    assert len(commands11) == 341
    assert failure11["successful_prefix_pushes"] == 112
    assert failure11["failed_command"] == (267, "west")
    assert failure11["support"] == 268 and not failure11["support_reachable"]

    model12 = Model("soko1_2")
    _, commands12, _, _ = replay(model12, witness("12"))
    early_park = commands12[32:36]
    assert early_park == [(189, "south"), (215, "west"), (214, "west"), (213, "west")]
    candidate12 = (commands12[:20] + early_park + commands12[20:31] +
                   commands12[36:44] + commands12[56:65] + commands12[44:55] + commands12[65:])
    failure12 = first_failure(model12, candidate12)
    assert len(candidate12) == 233
    assert failure12["successful_prefix_pushes"] == 20
    assert failure12["failed_command"] == (189, "south")
    assert failure12["support"] == 163 and not failure12["support_reachable"]

    sources = [Path(__file__).resolve(), HERE / "diagnose.py", HERE / "witness11_342.json",
               REPO / "lean/NetHack/Sokoban/Model.lean", REPO / "lean/NetHack/Sokoban/Maps.lean"]
    print(json.dumps(dict(
        task="nethack-invariants-codex-owner1007", configuration_search=False,
        method="Exactly two prescribed schedules; walking BFS only",
        validation_kind="Python diagnostic assertions, not kernel witnesses or lower bounds",
        source_sha256={str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in sources},
        cases=[dict(map="soko1-1", proposed_pushes=341, original_start=True,
                    change="Delete only original321East from checked342 schedule", result=failure11),
               dict(map="soko1-2", proposed_pushes=233, original_start=True,
                    change="Park original192 at212 before the Upper108/186 delivery and omit the187 reset",
                    result=failure12)]), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
