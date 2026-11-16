#!/usr/bin/env python3
"""Hand schedule removing the deep212 excursion; BFS connects walking only."""
import json
import re
from diagnose import Model, HERE
from emit_witness import emit_witness


def main():
    model = Model('soko1_1')
    state = model.initial
    labels = {c: c for c in state[1]}
    path, events = [], []

    def p(identity, code):
        nonlocal state
        tokens = re.findall(r'([NSEW])(\d+)', code)
        assert ''.join(d+n for d, n in tokens) == code
        for letter, count in tokens:
            direction = dict(N='north', S='south', E='east', W='west')[letter]
            for _ in range(int(count)):
                source = labels[identity]
                result = model.macros(state, [(source, direction)])
                assert result, (identity, code, source, state)
                state, walked = result
                landing = model.adjacent(source, direction)
                filled = landing not in state[1]
                if filled:
                    del labels[identity]
                else:
                    labels[identity] = landing
                events.append(dict(identity=identity, source=source, direction=direction,
                                   landing=landing, consumed=filled))
                path.extend(walked)

    def deliver(identity):
        first = len(state[2]) == 16
        p(identity, 'N3W1N3')
        if not first:
            p(identity, 'E1')

    # Shift268 and266 east, so212 can leave its shallow293 parking via267.
    for identity, code in [
        (264, 'W1'), (293, 'E1'), (321, 'E1'), (367, 'E3'),
        (317, 'E2S3W4N1E1'), (186, 'W2'), (268, 'E2'), (266, 'E1'),
        (212, 'E1S3E2'), (188, 'W2'), (191, 'W2'),
        (139, 'W1S3W3S3E1'), (137, 'E1S3W3S3')]:
        p(identity, code)
    for identity, code in [
        (191, 'E1'), (188, 'E4'), (186, 'E6'), (193, 'W3'),
        (137, 'N4E3'), (266, 'W2N3E3'), (212, 'N1W2N3E3'),
        (139, 'W1N4E3'), (264, 'E2N3E3'), (268, 'W5N3E3'),
        (293, 'W3N4E3'), (367, 'E1N4W2N3E3'), (317, 'E3N4W2N3E3'),
        (135, 'E3S3W3S3N4E3'), (133, 'E5S3W3S3N4E3'),
        (141, 'W3S3W3S3N4E3')]:
        p(identity, code)
        deliver(identity)
    assert len(events) == 342 and len(path) == 714 and not state[2]
    assert labels == {315: 315, 321: 322}
    report = emit_witness('soko1_1', path, 'Witness11_342')
    report.update(path=path, events=events, final_identities=labels,
                  method='One manual macro schedule; fixed-boulder walking BFS only')
    (HERE/'witness11_342.json').write_text(json.dumps(report, indent=2)+'\n')
    print('Explicit342-push/714-move plan generated; kernel check still required')


if __name__ == '__main__':
    main()
