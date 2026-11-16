#!/usr/bin/env python3
"""Four prescribed canonical prefixes; no search over boulder configurations.

The expected failures diagnose support and queue constraints. They prove no
universal lower bound and yield no winning witness. BFS connects walks only.
"""
import json
import re
from diagnose import Model, HERE

CASES = [
    ('budget327_right_park', [(212,'W2'), (186,'W1'), (188,'W1'), (191,'W2'),
                             (137,'E1S3E1')], (10,137,216,'east',215)),
    ('budget329_one_gate', [(186,'W2'), (212,'W2'), (188,'W2'), (191,'W2'),
                           (139,'W1S3W3S3'), (191,'E1N3W1N3')],
     (23,191,111,'north',137)),
    ('budget333_left_pair', [(264,'W1'), (186,'W2'), (212,'W2'), (188,'W2'),
                            (191,'W2'), (139,'W1S3W3S3E1'), (137,'E1S3W3S3'),
                            (191,'E1N3W1N3'), (188,'E4N3W1N3E1'), (186,'E6')],
     (50,186,184,'east',183)),
    ('budget331_shallow188', [(264,'W1'), (186,'W1'), (212,'W3'), (188,'W1'),
                             (191,'W2'), (139,'W1S3W3S3E1')],
     (15,139,213,'south',187)),
]


def trial(name, commands, expected):
    model = Model('soko1_1')
    state, labels = model.initial, {c:c for c in model.initial[1]}
    events, path = [], []
    for identity, code in commands:
        for letter, count in re.findall(r'([NSEW])(\d+)', code):
            direction = dict(N='north', S='south', E='east', W='west')[letter]
            for _ in range(int(count)):
                source = labels[identity]
                opposite = dict(north='south', south='north', east='west', west='east')
                support = model.adjacent(source, opposite[direction])
                result = model.macros(state, [(source,direction)])
                if result is None:
                    assert (len(events),identity,source,direction,support) == expected
                    assert support not in model.walks(state)
                    return dict(name=name, original_start=True,
                        result='expected_prescribed_prefix_failure', successful_pushes=len(events),
                        successful_moves=len(path), prescribed_macros=commands,
                        failed=dict(identity=identity,source=source,direction=direction,
                                    support=support,support_reachable=False),
                        state=dict(player=state[0],boulders=sorted(state[1]),holes=sorted(state[2])),
                        identities=labels,events=events)
                actual = model.step((support,state[1],state[2]),direction)
                assert actual and actual[1] and actual[0] == result[0]
                _, landing, filled = actual[1]
                state, walked = result
                if filled is not None:
                    del labels[identity]
                else:
                    labels[identity] = landing
                path.extend(walked)
                events.append(dict(identity=identity,source=source,direction=direction,
                                   landing=landing,filled=filled))
    raise AssertionError('Expected the specified failed prefix')


def main():
    report=dict(map='soko1-1',method='Exactly four prescribed canonical prefixes; walking BFS only',
                boulder_configuration_search=False,
                validation_scope='Python diagnostic assertions; no universal bound or winning witness',
                cases=[trial(*case) for case in CASES])
    (HERE/'gate_queue_handplans_diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
    for case in report['cases']:
        print(case['name'],case['successful_pushes'],case['failed'])

if __name__ == '__main__':
    main()
