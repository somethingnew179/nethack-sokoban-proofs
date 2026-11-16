#!/usr/bin/env python3
"""One hand-planned original-map diagnostic; no lower bound or Lean claim."""
import json
import re
from diagnose import Model, HERE

def main():
    model=Model("soko1_1")
    state=model.initial
    labels={cell:cell for cell in state[1]}
    path=[]
    events=[]
    directions=dict(N="north",S="south",E="east",W="west")
    def p(identity,code):
        nonlocal state
        tokens=re.findall(r"([NSEW])(\d+)",code)
        assert "".join(d+n for d,n in tokens)==code
        for letter,n in tokens:
            d=directions[letter]
            for _ in range(int(n)):
                source=labels[identity]
                result=model.macros(state,[(source,d)])
                assert result, (identity,code,source)
                after,walk=result
                actor=model.adjacent(source,dict(north="south",south="north",east="west",west="east")[d])
                checked=model.step((actor,state[1],state[2]),d)
                assert checked and checked[1]
                _,landing,filled=checked[1]
                if filled is None:labels[identity]=landing
                else:del labels[identity]
                events.append(dict(identity=identity,source=source,landing=landing,filled=filled))
                path.extend(walk)
                state=after
    def D(identity):
        first=len(state[2])==16
        p(identity,"N3W1N3")
        if not first:p(identity,"E1")
    for identity,code in [(133,"W1"),(135,"W2"),(264,"W1"),(293,"E3"),(367,"E3"),
        (317,"E2S3W4N1E1"),(186,"W2"),(212,"E1S3E1"),(188,"W2"),(191,"W2"),
        (139,"W1S3W3S3"),(191,"E1N3W3"),(137,"E1S3E1")]:p(identity,code)
    p(188,"E4");D(188)
    p(186,"E6");D(186)
    p(137,"W3")
    p(193,"W3");D(193)
    p(139,"N4E3");D(139)
    p(212,"W1N4E3");D(212)
    p(191,"E2N3E1")
    for identity,code in [(137,"W1S3N4E3"),(264,"E2N3E3"),(266,"W1N3E3"),
        (268,"W3N3E3"),(293,"W5N4E3"),(367,"E1N4W2N3E3"),
        (317,"E3N4W2N3E3"),(315,"E4S3W4N1E4N4W2N3E3"),
        (321,"W2S3W4N1E4N4W2N3E3"),(141,"W3S3W3S3N4E3")]:
        p(identity,code);D(identity)
    deep=[e for e in events if e["identity"]<26*12 and e["source"]//26==11 and e["landing"]//26==12]
    assert len(events)==358 and len(path)==723 and not state[2] and not deep
    result=dict(scope="Python diagnostic only; not a new Lean theorem",pushes=358,moves=723,
        upper_origin_row11_to_row12_pushes=deep,final_survivors=labels,path=path,events=events)
    (HERE/"no_deep_diagnostic11.json").write_text(json.dumps(result,indent=2)+"\n")
    print("PASS single explicit Python replay:358/723, no upper-origin row11→12 push; not a lower bound")

if __name__=="__main__":main()
