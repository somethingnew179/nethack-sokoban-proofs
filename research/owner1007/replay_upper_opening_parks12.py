#!/usr/bin/env python3
"""Three prescribed original-map prefixes, with walking BFS only.

These failures refute particular schedule changes; they prove no universal
bound, and do not certify a winning trace or search boulder configurations.
"""
import json
from diagnose import Model, HERE, replay, witness
from replay_park_reorder_failures import first_failure


def main():
    model = Model('soko1_2')
    _, commands, _, _ = replay(model, witness('12'))
    cases = []
    for name, park in [('park158_at133', [(132,'east')]),
                       ('park158_at134', [(132,'east'),(133,'east')])]:
        trial = commands[:19] + park + [(108,'north')]
        failed = first_failure(model, trial)
        assert failed['successful_prefix_pushes'] == 19 + len(park)
        assert failed['failed_command'] == (108,'north')
        assert failed['support'] == 134 and not failed['support_reachable']
        cases.append(dict(name=name, commands=trial, result=failed))
    trial = commands[:14] + [(213,'west'),(263,'west'),(237,'north'),
                            (238,'west'),(159,'north')]
    failed = first_failure(model, trial)
    assert failed['successful_prefix_pushes'] == 18
    assert failed['failed_command'] == (159,'north')
    assert failed['support'] == 185 and not failed['support_reachable']
    cases.append(dict(name='retain210_while_reordering_upper',commands=trial,result=failed))
    report = dict(map='soko1-2', original_canonical_start=True,
                  boulder_configuration_search=False,
                  method='Exactly three prescribed prefixes; walking BFS only',
                  scope='Python diagnostic assertions; no lower theorem or upper witness',cases=cases)
    (HERE/'upper_opening_parks12_diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
    for case in cases:
        print(case['name'], case['result']['successful_prefix_pushes'],
              case['result']['failed_command'], case['result']['support'])


if __name__ == '__main__':
    main()
