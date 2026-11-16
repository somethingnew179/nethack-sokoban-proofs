#!/usr/bin/env python3
"""Emit28 single-token zero-price frames; no multi-boulder states or search."""
from diagnose import HERE


def main():
    broad = {0,4,5,6,10,14,15,16,20,24,25,26,27}
    for letter, indices in [('A', range(14)), ('B', range(14,28))]:
        out = ['import Owner1007.ZeroWord11Data\n',
               'namespace Owner1007.ZeroWord11\n',
               'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
        for i in indices:
            if i in broad:
                out.append(
                    f'theorem walk{i} : walkNodeCheck {i} = true := by\n'
                    '  apply walk_of_closed\n'
                    '  intro hero inside dir target adjacent floor door different notHole clear\n'
                    f'  exact full_remove_walk (cell {i}) hero target dir inside adjacent floor different notHole\n')
            else:
                out.append(f'theorem walk{i} : walkNodeCheck {i} = true := by decide +kernel\n')
            out.append(f'theorem push{i} : pushNodeCheck {i} = true := by decide +kernel\n')
            out.append(f'theorem node{i} : nodeCheck {i} = true := Bool.and_eq_true_iff.mpr ⟨walk{i}, push{i}⟩\n')
        out.append(f'#print axioms node{indices[-1]}\nend Owner1007.ZeroWord11\n')
        (HERE/f'Owner1007/ZeroWord11Checks{letter}.lean').write_text(''.join(out))
    print('Generated28 local one-token frames in two kernel-check modules')


if __name__ == '__main__':
    main()
