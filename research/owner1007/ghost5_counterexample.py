#!/usr/bin/env python3
"""Replay one existing group7 abstract plan, not a search of puzzle states."""
import json
import re
from diagnose import Model, HERE, REPO

PREFIX = [105,119,123,97,107,141,143,147,115,58,110,113,145,124,
          110,123,141,143,145,124,147,113,110,147,113,147,133]
SUFFIX = [129,131,135,139,141,143,145,124,110,113,147,
          119,135,139,141,143,145,124,110,113,147]

def main():
    text = (REPO / "lean/NetHack/Soko32Penalty5/Data.lean").read_text()
    rows = re.findall(r"⟨(\d+), (\d+), (some \d+|none), (true|false), (\d+)⟩", text)
    assert len(rows) == 148
    model = Model("soko3_2")
    hero = model.initial[0]
    boxes = frozenset([139,215,239,244,267,270,289])
    total = walks = 0
    events = []
    for step,index in enumerate(PREFIX+SUFFIX):
        support,source,landing,discard,cost = rows[index]
        support,source,cost = int(support),int(source),int(cost)
        landing = None if landing == "none" else int(landing.split()[1])
        # The relaxation ignores holes. A sentinel keeps the walking-only
        # Model helper active and lies outside the finite board.
        reach = model.walks((hero,boxes,frozenset([-1])))
        assert support in reach and source in boxes and (landing is None or landing not in boxes), (step,index)
        walked = reach[support]
        walks += len(walked)
        boxes = boxes - {source}
        if landing is not None and discard == "false":
            boxes = boxes | {landing}
        hero = source
        total += cost
        events.append(dict(action=index,walk=walked,slack=cost,hero=hero,boxes=sorted(boxes)))
        if step+1 == len(PREFIX):
            assert total == 5 and boxes == {265,289} and hero == 291
    assert total == 5 and not boxes
    result = dict(scope="group7 relaxation ONLY; not an original completing legal trace",
                  total_slack=total,abstract_pushes=len(events),walking_moves=walks,final_hero=hero,events=events)
    (HERE / "ghost5_counterexample.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "events"}))

if __name__ == "__main__":main()
