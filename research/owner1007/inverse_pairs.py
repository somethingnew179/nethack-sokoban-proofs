#!/usr/bin/env python3
"""Try deleting only consecutive inverse pushes of the SAME labelled stone."""
import json
from diagnose import Model, witness, replay, HERE

def main():
    reports = {}
    for tag,name in [("11","soko1_1"),("12","soko1_2"),("32","soko3_2")]:
        model=Model(name)
        _,commands,events,_=replay(model,witness(tag))
        previous={}
        tested=[]
        found=[]
        for i,event in enumerate(events):
            identity=event["identity"]
            if identity in previous:
                j=previous[identity]
                earlier=events[j]
                if earlier["source"]==event["landing"] and earlier["landing"]==event["source"] and earlier["filled"] is None and event["filled"] is None:
                    result=model.macros(model.initial,[c for k,c in enumerate(commands) if k not in [j,i]])
                    tested.append([j+1,i+1])
                    if result and not result[0][2]:
                        found.append(dict(removed=[j+1,i+1],pushes=len(commands)-2,moves=len(result[1]),path=result[1]))
            previous[identity]=i
        reports[name]=dict(tested=tested,improvements=found)
        print(name,"inverse_pairs",len(tested),"improvements",len(found))
    (HERE/"inverse_pair_checks.json").write_text(json.dumps(reports,indent=2)+"\n")

if __name__=="__main__":main()
