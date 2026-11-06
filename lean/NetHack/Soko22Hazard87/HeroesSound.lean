import NetHack.Soko22Hazard87.OracleSound013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem heroSound25 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound0 p outcome checked decreasing
  | south => exact oracleSound1 p outcome checked decreasing
  | east => exact oracleSound2 p outcome checked decreasing
  | west => exact oracleSound3 p outcome checked decreasing
  | northEast => exact oracleSound4 p outcome checked decreasing
  | northWest => exact oracleSound5 p outcome checked decreasing
  | southEast => exact oracleSound6 p outcome checked decreasing
  | southWest => exact oracleSound7 p outcome checked decreasing
theorem heroSound27 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound8 p outcome checked decreasing
  | south => exact oracleSound9 p outcome checked decreasing
  | east => exact oracleSound10 p outcome checked decreasing
  | west => exact oracleSound11 p outcome checked decreasing
  | northEast => exact oracleSound12 p outcome checked decreasing
  | northWest => exact oracleSound13 p outcome checked decreasing
  | southEast => exact oracleSound14 p outcome checked decreasing
  | southWest => exact oracleSound15 p outcome checked decreasing
theorem heroSound28 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound16 p outcome checked decreasing
  | south => exact oracleSound17 p outcome checked decreasing
  | east => exact oracleSound18 p outcome checked decreasing
  | west => exact oracleSound19 p outcome checked decreasing
  | northEast => exact oracleSound20 p outcome checked decreasing
  | northWest => exact oracleSound21 p outcome checked decreasing
  | southEast => exact oracleSound22 p outcome checked decreasing
  | southWest => exact oracleSound23 p outcome checked decreasing
theorem heroSound29 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound24 p outcome checked decreasing
  | south => exact oracleSound25 p outcome checked decreasing
  | east => exact oracleSound26 p outcome checked decreasing
  | west => exact oracleSound27 p outcome checked decreasing
  | northEast => exact oracleSound28 p outcome checked decreasing
  | northWest => exact oracleSound29 p outcome checked decreasing
  | southEast => exact oracleSound30 p outcome checked decreasing
  | southWest => exact oracleSound31 p outcome checked decreasing
theorem heroSound30 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound32 p outcome checked decreasing
  | south => exact oracleSound33 p outcome checked decreasing
  | east => exact oracleSound34 p outcome checked decreasing
  | west => exact oracleSound35 p outcome checked decreasing
  | northEast => exact oracleSound36 p outcome checked decreasing
  | northWest => exact oracleSound37 p outcome checked decreasing
  | southEast => exact oracleSound38 p outcome checked decreasing
  | southWest => exact oracleSound39 p outcome checked decreasing
theorem heroSound45 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound40 p outcome checked decreasing
  | south => exact oracleSound41 p outcome checked decreasing
  | east => exact oracleSound42 p outcome checked decreasing
  | west => exact oracleSound43 p outcome checked decreasing
  | northEast => exact oracleSound44 p outcome checked decreasing
  | northWest => exact oracleSound45 p outcome checked decreasing
  | southEast => exact oracleSound46 p outcome checked decreasing
  | southWest => exact oracleSound47 p outcome checked decreasing
theorem heroSound46 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound48 p outcome checked decreasing
  | south => exact oracleSound49 p outcome checked decreasing
  | east => exact oracleSound50 p outcome checked decreasing
  | west => exact oracleSound51 p outcome checked decreasing
  | northEast => exact oracleSound52 p outcome checked decreasing
  | northWest => exact oracleSound53 p outcome checked decreasing
  | southEast => exact oracleSound54 p outcome checked decreasing
  | southWest => exact oracleSound55 p outcome checked decreasing
theorem heroSound47 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound56 p outcome checked decreasing
  | south => exact oracleSound57 p outcome checked decreasing
  | east => exact oracleSound58 p outcome checked decreasing
  | west => exact oracleSound59 p outcome checked decreasing
  | northEast => exact oracleSound60 p outcome checked decreasing
  | northWest => exact oracleSound61 p outcome checked decreasing
  | southEast => exact oracleSound62 p outcome checked decreasing
  | southWest => exact oracleSound63 p outcome checked decreasing
theorem heroSound48 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound64 p outcome checked decreasing
  | south => exact oracleSound65 p outcome checked decreasing
  | east => exact oracleSound66 p outcome checked decreasing
  | west => exact oracleSound67 p outcome checked decreasing
  | northEast => exact oracleSound68 p outcome checked decreasing
  | northWest => exact oracleSound69 p outcome checked decreasing
  | southEast => exact oracleSound70 p outcome checked decreasing
  | southWest => exact oracleSound71 p outcome checked decreasing
theorem heroSound49 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound72 p outcome checked decreasing
  | south => exact oracleSound73 p outcome checked decreasing
  | east => exact oracleSound74 p outcome checked decreasing
  | west => exact oracleSound75 p outcome checked decreasing
  | northEast => exact oracleSound76 p outcome checked decreasing
  | northWest => exact oracleSound77 p outcome checked decreasing
  | southEast => exact oracleSound78 p outcome checked decreasing
  | southWest => exact oracleSound79 p outcome checked decreasing
theorem heroSound50 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 50 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 50 p) :
    NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 50 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound80 p outcome checked decreasing
  | south => exact oracleSound81 p outcome checked decreasing
  | east => exact oracleSound82 p outcome checked decreasing
  | west => exact oracleSound83 p outcome checked decreasing
  | northEast => exact oracleSound84 p outcome checked decreasing
  | northWest => exact oracleSound85 p outcome checked decreasing
  | southEast => exact oracleSound86 p outcome checked decreasing
  | southWest => exact oracleSound87 p outcome checked decreasing
theorem heroSound51 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 51 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 51 p) :
    NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 51 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound88 p outcome checked decreasing
  | south => exact oracleSound89 p outcome checked decreasing
  | east => exact oracleSound90 p outcome checked decreasing
  | west => exact oracleSound91 p outcome checked decreasing
  | northEast => exact oracleSound92 p outcome checked decreasing
  | northWest => exact oracleSound93 p outcome checked decreasing
  | southEast => exact oracleSound94 p outcome checked decreasing
  | southWest => exact oracleSound95 p outcome checked decreasing
theorem heroSound52 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 52 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 52 p) :
    NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 52 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound96 p outcome checked decreasing
  | south => exact oracleSound97 p outcome checked decreasing
  | east => exact oracleSound98 p outcome checked decreasing
  | west => exact oracleSound99 p outcome checked decreasing
  | northEast => exact oracleSound100 p outcome checked decreasing
  | northWest => exact oracleSound101 p outcome checked decreasing
  | southEast => exact oracleSound102 p outcome checked decreasing
  | southWest => exact oracleSound103 p outcome checked decreasing
theorem heroSound67 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 67 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 67 p) :
    NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 67 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound104 p outcome checked decreasing
  | south => exact oracleSound105 p outcome checked decreasing
  | east => exact oracleSound106 p outcome checked decreasing
  | west => exact oracleSound107 p outcome checked decreasing
  | northEast => exact oracleSound108 p outcome checked decreasing
  | northWest => exact oracleSound109 p outcome checked decreasing
  | southEast => exact oracleSound110 p outcome checked decreasing
  | southWest => exact oracleSound111 p outcome checked decreasing
theorem heroSound69 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 69 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 69 p) :
    NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 69 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound112 p outcome checked decreasing
  | south => exact oracleSound113 p outcome checked decreasing
  | east => exact oracleSound114 p outcome checked decreasing
  | west => exact oracleSound115 p outcome checked decreasing
  | northEast => exact oracleSound116 p outcome checked decreasing
  | northWest => exact oracleSound117 p outcome checked decreasing
  | southEast => exact oracleSound118 p outcome checked decreasing
  | southWest => exact oracleSound119 p outcome checked decreasing
theorem heroSound70 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 70 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 70 p) :
    NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 70 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound120 p outcome checked decreasing
  | south => exact oracleSound121 p outcome checked decreasing
  | east => exact oracleSound122 p outcome checked decreasing
  | west => exact oracleSound123 p outcome checked decreasing
  | northEast => exact oracleSound124 p outcome checked decreasing
  | northWest => exact oracleSound125 p outcome checked decreasing
  | southEast => exact oracleSound126 p outcome checked decreasing
  | southWest => exact oracleSound127 p outcome checked decreasing
theorem heroSound71 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 71 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 71 p) :
    NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 71 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound128 p outcome checked decreasing
  | south => exact oracleSound129 p outcome checked decreasing
  | east => exact oracleSound130 p outcome checked decreasing
  | west => exact oracleSound131 p outcome checked decreasing
  | northEast => exact oracleSound132 p outcome checked decreasing
  | northWest => exact oracleSound133 p outcome checked decreasing
  | southEast => exact oracleSound134 p outcome checked decreasing
  | southWest => exact oracleSound135 p outcome checked decreasing
theorem heroSound73 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 73 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 73 p) :
    NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 73 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound136 p outcome checked decreasing
  | south => exact oracleSound137 p outcome checked decreasing
  | east => exact oracleSound138 p outcome checked decreasing
  | west => exact oracleSound139 p outcome checked decreasing
  | northEast => exact oracleSound140 p outcome checked decreasing
  | northWest => exact oracleSound141 p outcome checked decreasing
  | southEast => exact oracleSound142 p outcome checked decreasing
  | southWest => exact oracleSound143 p outcome checked decreasing
theorem heroSound74 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 74 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 74 p) :
    NetHack.Sokoban22Refined85.bonus 74 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 74 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound144 p outcome checked decreasing
  | south => exact oracleSound145 p outcome checked decreasing
  | east => exact oracleSound146 p outcome checked decreasing
  | west => exact oracleSound147 p outcome checked decreasing
  | northEast => exact oracleSound148 p outcome checked decreasing
  | northWest => exact oracleSound149 p outcome checked decreasing
  | southEast => exact oracleSound150 p outcome checked decreasing
  | southWest => exact oracleSound151 p outcome checked decreasing
theorem heroSound76 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 76 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 76 p) :
    NetHack.Sokoban22Refined85.bonus 76 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 76 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound152 p outcome checked decreasing
  | south => exact oracleSound153 p outcome checked decreasing
  | east => exact oracleSound154 p outcome checked decreasing
  | west => exact oracleSound155 p outcome checked decreasing
  | northEast => exact oracleSound156 p outcome checked decreasing
  | northWest => exact oracleSound157 p outcome checked decreasing
  | southEast => exact oracleSound158 p outcome checked decreasing
  | southWest => exact oracleSound159 p outcome checked decreasing
theorem heroSound78 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 78 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 78 p) :
    NetHack.Sokoban22Refined85.bonus 78 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 78 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound160 p outcome checked decreasing
  | south => exact oracleSound161 p outcome checked decreasing
  | east => exact oracleSound162 p outcome checked decreasing
  | west => exact oracleSound163 p outcome checked decreasing
  | northEast => exact oracleSound164 p outcome checked decreasing
  | northWest => exact oracleSound165 p outcome checked decreasing
  | southEast => exact oracleSound166 p outcome checked decreasing
  | southWest => exact oracleSound167 p outcome checked decreasing
theorem heroSound79 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 79 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 79 p) :
    NetHack.Sokoban22Refined85.bonus 79 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 79 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound168 p outcome checked decreasing
  | south => exact oracleSound169 p outcome checked decreasing
  | east => exact oracleSound170 p outcome checked decreasing
  | west => exact oracleSound171 p outcome checked decreasing
  | northEast => exact oracleSound172 p outcome checked decreasing
  | northWest => exact oracleSound173 p outcome checked decreasing
  | southEast => exact oracleSound174 p outcome checked decreasing
  | southWest => exact oracleSound175 p outcome checked decreasing
theorem heroSound80 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 80 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 80 p) :
    NetHack.Sokoban22Refined85.bonus 80 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 80 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound176 p outcome checked decreasing
  | south => exact oracleSound177 p outcome checked decreasing
  | east => exact oracleSound178 p outcome checked decreasing
  | west => exact oracleSound179 p outcome checked decreasing
  | northEast => exact oracleSound180 p outcome checked decreasing
  | northWest => exact oracleSound181 p outcome checked decreasing
  | southEast => exact oracleSound182 p outcome checked decreasing
  | southWest => exact oracleSound183 p outcome checked decreasing
theorem heroSound81 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 81 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 81 p) :
    NetHack.Sokoban22Refined85.bonus 81 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 81 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound184 p outcome checked decreasing
  | south => exact oracleSound185 p outcome checked decreasing
  | east => exact oracleSound186 p outcome checked decreasing
  | west => exact oracleSound187 p outcome checked decreasing
  | northEast => exact oracleSound188 p outcome checked decreasing
  | northWest => exact oracleSound189 p outcome checked decreasing
  | southEast => exact oracleSound190 p outcome checked decreasing
  | southWest => exact oracleSound191 p outcome checked decreasing
theorem heroSound82 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 82 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 82 p) :
    NetHack.Sokoban22Refined85.bonus 82 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 82 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound192 p outcome checked decreasing
  | south => exact oracleSound193 p outcome checked decreasing
  | east => exact oracleSound194 p outcome checked decreasing
  | west => exact oracleSound195 p outcome checked decreasing
  | northEast => exact oracleSound196 p outcome checked decreasing
  | northWest => exact oracleSound197 p outcome checked decreasing
  | southEast => exact oracleSound198 p outcome checked decreasing
  | southWest => exact oracleSound199 p outcome checked decreasing
theorem heroSound83 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 83 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 83 p) :
    NetHack.Sokoban22Refined85.bonus 83 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 83 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound200 p outcome checked decreasing
  | south => exact oracleSound201 p outcome checked decreasing
  | east => exact oracleSound202 p outcome checked decreasing
  | west => exact oracleSound203 p outcome checked decreasing
  | northEast => exact oracleSound204 p outcome checked decreasing
  | northWest => exact oracleSound205 p outcome checked decreasing
  | southEast => exact oracleSound206 p outcome checked decreasing
  | southWest => exact oracleSound207 p outcome checked decreasing
theorem heroSound84 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 84 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 84 p) :
    NetHack.Sokoban22Refined85.bonus 84 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 84 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound208 p outcome checked decreasing
  | south => exact oracleSound209 p outcome checked decreasing
  | east => exact oracleSound210 p outcome checked decreasing
  | west => exact oracleSound211 p outcome checked decreasing
  | northEast => exact oracleSound212 p outcome checked decreasing
  | northWest => exact oracleSound213 p outcome checked decreasing
  | southEast => exact oracleSound214 p outcome checked decreasing
  | southWest => exact oracleSound215 p outcome checked decreasing
theorem heroSound89 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 89 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 89 p) :
    NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 89 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound216 p outcome checked decreasing
  | south => exact oracleSound217 p outcome checked decreasing
  | east => exact oracleSound218 p outcome checked decreasing
  | west => exact oracleSound219 p outcome checked decreasing
  | northEast => exact oracleSound220 p outcome checked decreasing
  | northWest => exact oracleSound221 p outcome checked decreasing
  | southEast => exact oracleSound222 p outcome checked decreasing
  | southWest => exact oracleSound223 p outcome checked decreasing
theorem heroSound90 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 90 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 90 p) :
    NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 90 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound224 p outcome checked decreasing
  | south => exact oracleSound225 p outcome checked decreasing
  | east => exact oracleSound226 p outcome checked decreasing
  | west => exact oracleSound227 p outcome checked decreasing
  | northEast => exact oracleSound228 p outcome checked decreasing
  | northWest => exact oracleSound229 p outcome checked decreasing
  | southEast => exact oracleSound230 p outcome checked decreasing
  | southWest => exact oracleSound231 p outcome checked decreasing
theorem heroSound91 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 91 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 91 p) :
    NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 91 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound232 p outcome checked decreasing
  | south => exact oracleSound233 p outcome checked decreasing
  | east => exact oracleSound234 p outcome checked decreasing
  | west => exact oracleSound235 p outcome checked decreasing
  | northEast => exact oracleSound236 p outcome checked decreasing
  | northWest => exact oracleSound237 p outcome checked decreasing
  | southEast => exact oracleSound238 p outcome checked decreasing
  | southWest => exact oracleSound239 p outcome checked decreasing
theorem heroSound93 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound240 p outcome checked decreasing
  | south => exact oracleSound241 p outcome checked decreasing
  | east => exact oracleSound242 p outcome checked decreasing
  | west => exact oracleSound243 p outcome checked decreasing
  | northEast => exact oracleSound244 p outcome checked decreasing
  | northWest => exact oracleSound245 p outcome checked decreasing
  | southEast => exact oracleSound246 p outcome checked decreasing
  | southWest => exact oracleSound247 p outcome checked decreasing
theorem heroSound94 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound248 p outcome checked decreasing
  | south => exact oracleSound249 p outcome checked decreasing
  | east => exact oracleSound250 p outcome checked decreasing
  | west => exact oracleSound251 p outcome checked decreasing
  | northEast => exact oracleSound252 p outcome checked decreasing
  | northWest => exact oracleSound253 p outcome checked decreasing
  | southEast => exact oracleSound254 p outcome checked decreasing
  | southWest => exact oracleSound255 p outcome checked decreasing
theorem heroSound95 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound256 p outcome checked decreasing
  | south => exact oracleSound257 p outcome checked decreasing
  | east => exact oracleSound258 p outcome checked decreasing
  | west => exact oracleSound259 p outcome checked decreasing
  | northEast => exact oracleSound260 p outcome checked decreasing
  | northWest => exact oracleSound261 p outcome checked decreasing
  | southEast => exact oracleSound262 p outcome checked decreasing
  | southWest => exact oracleSound263 p outcome checked decreasing
theorem heroSound96 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound264 p outcome checked decreasing
  | south => exact oracleSound265 p outcome checked decreasing
  | east => exact oracleSound266 p outcome checked decreasing
  | west => exact oracleSound267 p outcome checked decreasing
  | northEast => exact oracleSound268 p outcome checked decreasing
  | northWest => exact oracleSound269 p outcome checked decreasing
  | southEast => exact oracleSound270 p outcome checked decreasing
  | southWest => exact oracleSound271 p outcome checked decreasing
theorem heroSound97 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound272 p outcome checked decreasing
  | south => exact oracleSound273 p outcome checked decreasing
  | east => exact oracleSound274 p outcome checked decreasing
  | west => exact oracleSound275 p outcome checked decreasing
  | northEast => exact oracleSound276 p outcome checked decreasing
  | northWest => exact oracleSound277 p outcome checked decreasing
  | southEast => exact oracleSound278 p outcome checked decreasing
  | southWest => exact oracleSound279 p outcome checked decreasing
theorem heroSound98 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound280 p outcome checked decreasing
  | south => exact oracleSound281 p outcome checked decreasing
  | east => exact oracleSound282 p outcome checked decreasing
  | west => exact oracleSound283 p outcome checked decreasing
  | northEast => exact oracleSound284 p outcome checked decreasing
  | northWest => exact oracleSound285 p outcome checked decreasing
  | southEast => exact oracleSound286 p outcome checked decreasing
  | southWest => exact oracleSound287 p outcome checked decreasing
theorem heroSound100 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound288 p outcome checked decreasing
  | south => exact oracleSound289 p outcome checked decreasing
  | east => exact oracleSound290 p outcome checked decreasing
  | west => exact oracleSound291 p outcome checked decreasing
  | northEast => exact oracleSound292 p outcome checked decreasing
  | northWest => exact oracleSound293 p outcome checked decreasing
  | southEast => exact oracleSound294 p outcome checked decreasing
  | southWest => exact oracleSound295 p outcome checked decreasing
theorem heroSound101 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound296 p outcome checked decreasing
  | south => exact oracleSound297 p outcome checked decreasing
  | east => exact oracleSound298 p outcome checked decreasing
  | west => exact oracleSound299 p outcome checked decreasing
  | northEast => exact oracleSound300 p outcome checked decreasing
  | northWest => exact oracleSound301 p outcome checked decreasing
  | southEast => exact oracleSound302 p outcome checked decreasing
  | southWest => exact oracleSound303 p outcome checked decreasing
theorem heroSound102 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound304 p outcome checked decreasing
  | south => exact oracleSound305 p outcome checked decreasing
  | east => exact oracleSound306 p outcome checked decreasing
  | west => exact oracleSound307 p outcome checked decreasing
  | northEast => exact oracleSound308 p outcome checked decreasing
  | northWest => exact oracleSound309 p outcome checked decreasing
  | southEast => exact oracleSound310 p outcome checked decreasing
  | southWest => exact oracleSound311 p outcome checked decreasing
theorem heroSound103 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound312 p outcome checked decreasing
  | south => exact oracleSound313 p outcome checked decreasing
  | east => exact oracleSound314 p outcome checked decreasing
  | west => exact oracleSound315 p outcome checked decreasing
  | northEast => exact oracleSound316 p outcome checked decreasing
  | northWest => exact oracleSound317 p outcome checked decreasing
  | southEast => exact oracleSound318 p outcome checked decreasing
  | southWest => exact oracleSound319 p outcome checked decreasing
theorem heroSound104 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound320 p outcome checked decreasing
  | south => exact oracleSound321 p outcome checked decreasing
  | east => exact oracleSound322 p outcome checked decreasing
  | west => exact oracleSound323 p outcome checked decreasing
  | northEast => exact oracleSound324 p outcome checked decreasing
  | northWest => exact oracleSound325 p outcome checked decreasing
  | southEast => exact oracleSound326 p outcome checked decreasing
  | southWest => exact oracleSound327 p outcome checked decreasing
theorem heroSound105 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound328 p outcome checked decreasing
  | south => exact oracleSound329 p outcome checked decreasing
  | east => exact oracleSound330 p outcome checked decreasing
  | west => exact oracleSound331 p outcome checked decreasing
  | northEast => exact oracleSound332 p outcome checked decreasing
  | northWest => exact oracleSound333 p outcome checked decreasing
  | southEast => exact oracleSound334 p outcome checked decreasing
  | southWest => exact oracleSound335 p outcome checked decreasing
theorem heroSound106 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound336 p outcome checked decreasing
  | south => exact oracleSound337 p outcome checked decreasing
  | east => exact oracleSound338 p outcome checked decreasing
  | west => exact oracleSound339 p outcome checked decreasing
  | northEast => exact oracleSound340 p outcome checked decreasing
  | northWest => exact oracleSound341 p outcome checked decreasing
  | southEast => exact oracleSound342 p outcome checked decreasing
  | southWest => exact oracleSound343 p outcome checked decreasing
theorem heroSound111 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound344 p outcome checked decreasing
  | south => exact oracleSound345 p outcome checked decreasing
  | east => exact oracleSound346 p outcome checked decreasing
  | west => exact oracleSound347 p outcome checked decreasing
  | northEast => exact oracleSound348 p outcome checked decreasing
  | northWest => exact oracleSound349 p outcome checked decreasing
  | southEast => exact oracleSound350 p outcome checked decreasing
  | southWest => exact oracleSound351 p outcome checked decreasing
theorem heroSound113 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound352 p outcome checked decreasing
  | south => exact oracleSound353 p outcome checked decreasing
  | east => exact oracleSound354 p outcome checked decreasing
  | west => exact oracleSound355 p outcome checked decreasing
  | northEast => exact oracleSound356 p outcome checked decreasing
  | northWest => exact oracleSound357 p outcome checked decreasing
  | southEast => exact oracleSound358 p outcome checked decreasing
  | southWest => exact oracleSound359 p outcome checked decreasing
theorem heroSound114 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound360 p outcome checked decreasing
  | south => exact oracleSound361 p outcome checked decreasing
  | east => exact oracleSound362 p outcome checked decreasing
  | west => exact oracleSound363 p outcome checked decreasing
  | northEast => exact oracleSound364 p outcome checked decreasing
  | northWest => exact oracleSound365 p outcome checked decreasing
  | southEast => exact oracleSound366 p outcome checked decreasing
  | southWest => exact oracleSound367 p outcome checked decreasing
theorem heroSound115 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound368 p outcome checked decreasing
  | south => exact oracleSound369 p outcome checked decreasing
  | east => exact oracleSound370 p outcome checked decreasing
  | west => exact oracleSound371 p outcome checked decreasing
  | northEast => exact oracleSound372 p outcome checked decreasing
  | northWest => exact oracleSound373 p outcome checked decreasing
  | southEast => exact oracleSound374 p outcome checked decreasing
  | southWest => exact oracleSound375 p outcome checked decreasing
theorem heroSound116 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound376 p outcome checked decreasing
  | south => exact oracleSound377 p outcome checked decreasing
  | east => exact oracleSound378 p outcome checked decreasing
  | west => exact oracleSound379 p outcome checked decreasing
  | northEast => exact oracleSound380 p outcome checked decreasing
  | northWest => exact oracleSound381 p outcome checked decreasing
  | southEast => exact oracleSound382 p outcome checked decreasing
  | southWest => exact oracleSound383 p outcome checked decreasing
theorem heroSound118 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound384 p outcome checked decreasing
  | south => exact oracleSound385 p outcome checked decreasing
  | east => exact oracleSound386 p outcome checked decreasing
  | west => exact oracleSound387 p outcome checked decreasing
  | northEast => exact oracleSound388 p outcome checked decreasing
  | northWest => exact oracleSound389 p outcome checked decreasing
  | southEast => exact oracleSound390 p outcome checked decreasing
  | southWest => exact oracleSound391 p outcome checked decreasing
theorem heroSound119 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound392 p outcome checked decreasing
  | south => exact oracleSound393 p outcome checked decreasing
  | east => exact oracleSound394 p outcome checked decreasing
  | west => exact oracleSound395 p outcome checked decreasing
  | northEast => exact oracleSound396 p outcome checked decreasing
  | northWest => exact oracleSound397 p outcome checked decreasing
  | southEast => exact oracleSound398 p outcome checked decreasing
  | southWest => exact oracleSound399 p outcome checked decreasing
theorem heroSound120 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 120 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 120 p) :
    NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 120 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound400 p outcome checked decreasing
  | south => exact oracleSound401 p outcome checked decreasing
  | east => exact oracleSound402 p outcome checked decreasing
  | west => exact oracleSound403 p outcome checked decreasing
  | northEast => exact oracleSound404 p outcome checked decreasing
  | northWest => exact oracleSound405 p outcome checked decreasing
  | southEast => exact oracleSound406 p outcome checked decreasing
  | southWest => exact oracleSound407 p outcome checked decreasing
theorem heroSound122 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 122 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 122 p) :
    NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 122 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound408 p outcome checked decreasing
  | south => exact oracleSound409 p outcome checked decreasing
  | east => exact oracleSound410 p outcome checked decreasing
  | west => exact oracleSound411 p outcome checked decreasing
  | northEast => exact oracleSound412 p outcome checked decreasing
  | northWest => exact oracleSound413 p outcome checked decreasing
  | southEast => exact oracleSound414 p outcome checked decreasing
  | southWest => exact oracleSound415 p outcome checked decreasing
theorem heroSound123 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 123 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 123 p) :
    NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 123 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound416 p outcome checked decreasing
  | south => exact oracleSound417 p outcome checked decreasing
  | east => exact oracleSound418 p outcome checked decreasing
  | west => exact oracleSound419 p outcome checked decreasing
  | northEast => exact oracleSound420 p outcome checked decreasing
  | northWest => exact oracleSound421 p outcome checked decreasing
  | southEast => exact oracleSound422 p outcome checked decreasing
  | southWest => exact oracleSound423 p outcome checked decreasing
theorem heroSound124 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 124 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 124 p) :
    NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 124 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound424 p outcome checked decreasing
  | south => exact oracleSound425 p outcome checked decreasing
  | east => exact oracleSound426 p outcome checked decreasing
  | west => exact oracleSound427 p outcome checked decreasing
  | northEast => exact oracleSound428 p outcome checked decreasing
  | northWest => exact oracleSound429 p outcome checked decreasing
  | southEast => exact oracleSound430 p outcome checked decreasing
  | southWest => exact oracleSound431 p outcome checked decreasing
theorem heroSound125 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 125 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 125 p) :
    NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 125 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound432 p outcome checked decreasing
  | south => exact oracleSound433 p outcome checked decreasing
  | east => exact oracleSound434 p outcome checked decreasing
  | west => exact oracleSound435 p outcome checked decreasing
  | northEast => exact oracleSound436 p outcome checked decreasing
  | northWest => exact oracleSound437 p outcome checked decreasing
  | southEast => exact oracleSound438 p outcome checked decreasing
  | southWest => exact oracleSound439 p outcome checked decreasing
theorem heroSound126 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 126 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 126 p) :
    NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 126 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound440 p outcome checked decreasing
  | south => exact oracleSound441 p outcome checked decreasing
  | east => exact oracleSound442 p outcome checked decreasing
  | west => exact oracleSound443 p outcome checked decreasing
  | northEast => exact oracleSound444 p outcome checked decreasing
  | northWest => exact oracleSound445 p outcome checked decreasing
  | southEast => exact oracleSound446 p outcome checked decreasing
  | southWest => exact oracleSound447 p outcome checked decreasing
theorem heroSound127 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 127 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 127 p) :
    NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 127 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound448 p outcome checked decreasing
  | south => exact oracleSound449 p outcome checked decreasing
  | east => exact oracleSound450 p outcome checked decreasing
  | west => exact oracleSound451 p outcome checked decreasing
  | northEast => exact oracleSound452 p outcome checked decreasing
  | northWest => exact oracleSound453 p outcome checked decreasing
  | southEast => exact oracleSound454 p outcome checked decreasing
  | southWest => exact oracleSound455 p outcome checked decreasing
theorem heroSound128 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 128 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 128 p) :
    NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 128 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound456 p outcome checked decreasing
  | south => exact oracleSound457 p outcome checked decreasing
  | east => exact oracleSound458 p outcome checked decreasing
  | west => exact oracleSound459 p outcome checked decreasing
  | northEast => exact oracleSound460 p outcome checked decreasing
  | northWest => exact oracleSound461 p outcome checked decreasing
  | southEast => exact oracleSound462 p outcome checked decreasing
  | southWest => exact oracleSound463 p outcome checked decreasing
theorem heroSound133 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 133 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 133 p) :
    NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 133 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound464 p outcome checked decreasing
  | south => exact oracleSound465 p outcome checked decreasing
  | east => exact oracleSound466 p outcome checked decreasing
  | west => exact oracleSound467 p outcome checked decreasing
  | northEast => exact oracleSound468 p outcome checked decreasing
  | northWest => exact oracleSound469 p outcome checked decreasing
  | southEast => exact oracleSound470 p outcome checked decreasing
  | southWest => exact oracleSound471 p outcome checked decreasing
theorem heroSound134 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 134 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 134 p) :
    NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 134 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound472 p outcome checked decreasing
  | south => exact oracleSound473 p outcome checked decreasing
  | east => exact oracleSound474 p outcome checked decreasing
  | west => exact oracleSound475 p outcome checked decreasing
  | northEast => exact oracleSound476 p outcome checked decreasing
  | northWest => exact oracleSound477 p outcome checked decreasing
  | southEast => exact oracleSound478 p outcome checked decreasing
  | southWest => exact oracleSound479 p outcome checked decreasing
theorem heroSound135 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 135 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 135 p) :
    NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 135 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound480 p outcome checked decreasing
  | south => exact oracleSound481 p outcome checked decreasing
  | east => exact oracleSound482 p outcome checked decreasing
  | west => exact oracleSound483 p outcome checked decreasing
  | northEast => exact oracleSound484 p outcome checked decreasing
  | northWest => exact oracleSound485 p outcome checked decreasing
  | southEast => exact oracleSound486 p outcome checked decreasing
  | southWest => exact oracleSound487 p outcome checked decreasing
theorem heroSound136 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 136 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 136 p) :
    NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 136 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound488 p outcome checked decreasing
  | south => exact oracleSound489 p outcome checked decreasing
  | east => exact oracleSound490 p outcome checked decreasing
  | west => exact oracleSound491 p outcome checked decreasing
  | northEast => exact oracleSound492 p outcome checked decreasing
  | northWest => exact oracleSound493 p outcome checked decreasing
  | southEast => exact oracleSound494 p outcome checked decreasing
  | southWest => exact oracleSound495 p outcome checked decreasing
theorem heroSound138 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 138 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 138 p) :
    NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 138 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound496 p outcome checked decreasing
  | south => exact oracleSound497 p outcome checked decreasing
  | east => exact oracleSound498 p outcome checked decreasing
  | west => exact oracleSound499 p outcome checked decreasing
  | northEast => exact oracleSound500 p outcome checked decreasing
  | northWest => exact oracleSound501 p outcome checked decreasing
  | southEast => exact oracleSound502 p outcome checked decreasing
  | southWest => exact oracleSound503 p outcome checked decreasing
theorem heroSound141 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 141 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 141 p) :
    NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 141 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound504 p outcome checked decreasing
  | south => exact oracleSound505 p outcome checked decreasing
  | east => exact oracleSound506 p outcome checked decreasing
  | west => exact oracleSound507 p outcome checked decreasing
  | northEast => exact oracleSound508 p outcome checked decreasing
  | northWest => exact oracleSound509 p outcome checked decreasing
  | southEast => exact oracleSound510 p outcome checked decreasing
  | southWest => exact oracleSound511 p outcome checked decreasing
theorem heroSound144 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 144 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 144 p) :
    NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 144 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound512 p outcome checked decreasing
  | south => exact oracleSound513 p outcome checked decreasing
  | east => exact oracleSound514 p outcome checked decreasing
  | west => exact oracleSound515 p outcome checked decreasing
  | northEast => exact oracleSound516 p outcome checked decreasing
  | northWest => exact oracleSound517 p outcome checked decreasing
  | southEast => exact oracleSound518 p outcome checked decreasing
  | southWest => exact oracleSound519 p outcome checked decreasing
theorem heroSound145 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 145 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 145 p) :
    NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 145 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound520 p outcome checked decreasing
  | south => exact oracleSound521 p outcome checked decreasing
  | east => exact oracleSound522 p outcome checked decreasing
  | west => exact oracleSound523 p outcome checked decreasing
  | northEast => exact oracleSound524 p outcome checked decreasing
  | northWest => exact oracleSound525 p outcome checked decreasing
  | southEast => exact oracleSound526 p outcome checked decreasing
  | southWest => exact oracleSound527 p outcome checked decreasing
theorem heroSound146 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 146 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 146 p) :
    NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 146 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound528 p outcome checked decreasing
  | south => exact oracleSound529 p outcome checked decreasing
  | east => exact oracleSound530 p outcome checked decreasing
  | west => exact oracleSound531 p outcome checked decreasing
  | northEast => exact oracleSound532 p outcome checked decreasing
  | northWest => exact oracleSound533 p outcome checked decreasing
  | southEast => exact oracleSound534 p outcome checked decreasing
  | southWest => exact oracleSound535 p outcome checked decreasing
theorem heroSound147 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 147 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 147 p) :
    NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 147 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound536 p outcome checked decreasing
  | south => exact oracleSound537 p outcome checked decreasing
  | east => exact oracleSound538 p outcome checked decreasing
  | west => exact oracleSound539 p outcome checked decreasing
  | northEast => exact oracleSound540 p outcome checked decreasing
  | northWest => exact oracleSound541 p outcome checked decreasing
  | southEast => exact oracleSound542 p outcome checked decreasing
  | southWest => exact oracleSound543 p outcome checked decreasing
theorem heroSound148 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 148 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 148 p) :
    NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 148 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound544 p outcome checked decreasing
  | south => exact oracleSound545 p outcome checked decreasing
  | east => exact oracleSound546 p outcome checked decreasing
  | west => exact oracleSound547 p outcome checked decreasing
  | northEast => exact oracleSound548 p outcome checked decreasing
  | northWest => exact oracleSound549 p outcome checked decreasing
  | southEast => exact oracleSound550 p outcome checked decreasing
  | southWest => exact oracleSound551 p outcome checked decreasing
theorem heroSound149 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 149 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 149 p) :
    NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 149 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound552 p outcome checked decreasing
  | south => exact oracleSound553 p outcome checked decreasing
  | east => exact oracleSound554 p outcome checked decreasing
  | west => exact oracleSound555 p outcome checked decreasing
  | northEast => exact oracleSound556 p outcome checked decreasing
  | northWest => exact oracleSound557 p outcome checked decreasing
  | southEast => exact oracleSound558 p outcome checked decreasing
  | southWest => exact oracleSound559 p outcome checked decreasing
theorem heroSound150 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 150 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 150 p) :
    NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 150 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound560 p outcome checked decreasing
  | south => exact oracleSound561 p outcome checked decreasing
  | east => exact oracleSound562 p outcome checked decreasing
  | west => exact oracleSound563 p outcome checked decreasing
  | northEast => exact oracleSound564 p outcome checked decreasing
  | northWest => exact oracleSound565 p outcome checked decreasing
  | southEast => exact oracleSound566 p outcome checked decreasing
  | southWest => exact oracleSound567 p outcome checked decreasing
theorem heroSound155 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 155 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 155 p) :
    NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 155 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound568 p outcome checked decreasing
  | south => exact oracleSound569 p outcome checked decreasing
  | east => exact oracleSound570 p outcome checked decreasing
  | west => exact oracleSound571 p outcome checked decreasing
  | northEast => exact oracleSound572 p outcome checked decreasing
  | northWest => exact oracleSound573 p outcome checked decreasing
  | southEast => exact oracleSound574 p outcome checked decreasing
  | southWest => exact oracleSound575 p outcome checked decreasing
theorem heroSound156 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 156 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 156 p) :
    NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 156 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound576 p outcome checked decreasing
  | south => exact oracleSound577 p outcome checked decreasing
  | east => exact oracleSound578 p outcome checked decreasing
  | west => exact oracleSound579 p outcome checked decreasing
  | northEast => exact oracleSound580 p outcome checked decreasing
  | northWest => exact oracleSound581 p outcome checked decreasing
  | southEast => exact oracleSound582 p outcome checked decreasing
  | southWest => exact oracleSound583 p outcome checked decreasing
theorem heroSound157 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 157 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 157 p) :
    NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 157 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound584 p outcome checked decreasing
  | south => exact oracleSound585 p outcome checked decreasing
  | east => exact oracleSound586 p outcome checked decreasing
  | west => exact oracleSound587 p outcome checked decreasing
  | northEast => exact oracleSound588 p outcome checked decreasing
  | northWest => exact oracleSound589 p outcome checked decreasing
  | southEast => exact oracleSound590 p outcome checked decreasing
  | southWest => exact oracleSound591 p outcome checked decreasing
theorem heroSound158 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 158 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 158 p) :
    NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 158 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound592 p outcome checked decreasing
  | south => exact oracleSound593 p outcome checked decreasing
  | east => exact oracleSound594 p outcome checked decreasing
  | west => exact oracleSound595 p outcome checked decreasing
  | northEast => exact oracleSound596 p outcome checked decreasing
  | northWest => exact oracleSound597 p outcome checked decreasing
  | southEast => exact oracleSound598 p outcome checked decreasing
  | southWest => exact oracleSound599 p outcome checked decreasing
theorem heroSound159 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 159 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 159 p) :
    NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 159 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound600 p outcome checked decreasing
  | south => exact oracleSound601 p outcome checked decreasing
  | east => exact oracleSound602 p outcome checked decreasing
  | west => exact oracleSound603 p outcome checked decreasing
  | northEast => exact oracleSound604 p outcome checked decreasing
  | northWest => exact oracleSound605 p outcome checked decreasing
  | southEast => exact oracleSound606 p outcome checked decreasing
  | southWest => exact oracleSound607 p outcome checked decreasing
theorem heroSound160 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 160 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 160 p) :
    NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 160 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound608 p outcome checked decreasing
  | south => exact oracleSound609 p outcome checked decreasing
  | east => exact oracleSound610 p outcome checked decreasing
  | west => exact oracleSound611 p outcome checked decreasing
  | northEast => exact oracleSound612 p outcome checked decreasing
  | northWest => exact oracleSound613 p outcome checked decreasing
  | southEast => exact oracleSound614 p outcome checked decreasing
  | southWest => exact oracleSound615 p outcome checked decreasing
theorem heroSound161 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 161 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 161 p) :
    NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 161 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound616 p outcome checked decreasing
  | south => exact oracleSound617 p outcome checked decreasing
  | east => exact oracleSound618 p outcome checked decreasing
  | west => exact oracleSound619 p outcome checked decreasing
  | northEast => exact oracleSound620 p outcome checked decreasing
  | northWest => exact oracleSound621 p outcome checked decreasing
  | southEast => exact oracleSound622 p outcome checked decreasing
  | southWest => exact oracleSound623 p outcome checked decreasing
theorem heroSound162 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 162 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 162 p) :
    NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 162 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound624 p outcome checked decreasing
  | south => exact oracleSound625 p outcome checked decreasing
  | east => exact oracleSound626 p outcome checked decreasing
  | west => exact oracleSound627 p outcome checked decreasing
  | northEast => exact oracleSound628 p outcome checked decreasing
  | northWest => exact oracleSound629 p outcome checked decreasing
  | southEast => exact oracleSound630 p outcome checked decreasing
  | southWest => exact oracleSound631 p outcome checked decreasing
theorem heroSound163 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 163 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 163 p) :
    NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 163 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound632 p outcome checked decreasing
  | south => exact oracleSound633 p outcome checked decreasing
  | east => exact oracleSound634 p outcome checked decreasing
  | west => exact oracleSound635 p outcome checked decreasing
  | northEast => exact oracleSound636 p outcome checked decreasing
  | northWest => exact oracleSound637 p outcome checked decreasing
  | southEast => exact oracleSound638 p outcome checked decreasing
  | southWest => exact oracleSound639 p outcome checked decreasing
theorem heroSound164 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 164 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 164 p) :
    NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 164 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound640 p outcome checked decreasing
  | south => exact oracleSound641 p outcome checked decreasing
  | east => exact oracleSound642 p outcome checked decreasing
  | west => exact oracleSound643 p outcome checked decreasing
  | northEast => exact oracleSound644 p outcome checked decreasing
  | northWest => exact oracleSound645 p outcome checked decreasing
  | southEast => exact oracleSound646 p outcome checked decreasing
  | southWest => exact oracleSound647 p outcome checked decreasing
theorem heroSound166 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 166 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 166 p) :
    NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 166 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound648 p outcome checked decreasing
  | south => exact oracleSound649 p outcome checked decreasing
  | east => exact oracleSound650 p outcome checked decreasing
  | west => exact oracleSound651 p outcome checked decreasing
  | northEast => exact oracleSound652 p outcome checked decreasing
  | northWest => exact oracleSound653 p outcome checked decreasing
  | southEast => exact oracleSound654 p outcome checked decreasing
  | southWest => exact oracleSound655 p outcome checked decreasing
theorem heroSound167 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 167 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 167 p) :
    NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 167 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound656 p outcome checked decreasing
  | south => exact oracleSound657 p outcome checked decreasing
  | east => exact oracleSound658 p outcome checked decreasing
  | west => exact oracleSound659 p outcome checked decreasing
  | northEast => exact oracleSound660 p outcome checked decreasing
  | northWest => exact oracleSound661 p outcome checked decreasing
  | southEast => exact oracleSound662 p outcome checked decreasing
  | southWest => exact oracleSound663 p outcome checked decreasing
theorem heroSound168 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 168 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 168 p) :
    NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 168 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound664 p outcome checked decreasing
  | south => exact oracleSound665 p outcome checked decreasing
  | east => exact oracleSound666 p outcome checked decreasing
  | west => exact oracleSound667 p outcome checked decreasing
  | northEast => exact oracleSound668 p outcome checked decreasing
  | northWest => exact oracleSound669 p outcome checked decreasing
  | southEast => exact oracleSound670 p outcome checked decreasing
  | southWest => exact oracleSound671 p outcome checked decreasing
theorem heroSound169 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 169 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 169 p) :
    NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 169 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound672 p outcome checked decreasing
  | south => exact oracleSound673 p outcome checked decreasing
  | east => exact oracleSound674 p outcome checked decreasing
  | west => exact oracleSound675 p outcome checked decreasing
  | northEast => exact oracleSound676 p outcome checked decreasing
  | northWest => exact oracleSound677 p outcome checked decreasing
  | southEast => exact oracleSound678 p outcome checked decreasing
  | southWest => exact oracleSound679 p outcome checked decreasing
theorem heroSound170 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 170 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 170 p) :
    NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 170 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound680 p outcome checked decreasing
  | south => exact oracleSound681 p outcome checked decreasing
  | east => exact oracleSound682 p outcome checked decreasing
  | west => exact oracleSound683 p outcome checked decreasing
  | northEast => exact oracleSound684 p outcome checked decreasing
  | northWest => exact oracleSound685 p outcome checked decreasing
  | southEast => exact oracleSound686 p outcome checked decreasing
  | southWest => exact oracleSound687 p outcome checked decreasing
theorem heroSound171 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 171 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 171 p) :
    NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 171 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound688 p outcome checked decreasing
  | south => exact oracleSound689 p outcome checked decreasing
  | east => exact oracleSound690 p outcome checked decreasing
  | west => exact oracleSound691 p outcome checked decreasing
  | northEast => exact oracleSound692 p outcome checked decreasing
  | northWest => exact oracleSound693 p outcome checked decreasing
  | southEast => exact oracleSound694 p outcome checked decreasing
  | southWest => exact oracleSound695 p outcome checked decreasing
theorem heroSound172 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 172 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 172 p) :
    NetHack.Sokoban22Refined85.bonus 172 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 172 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound696 p outcome checked decreasing
  | south => exact oracleSound697 p outcome checked decreasing
  | east => exact oracleSound698 p outcome checked decreasing
  | west => exact oracleSound699 p outcome checked decreasing
  | northEast => exact oracleSound700 p outcome checked decreasing
  | northWest => exact oracleSound701 p outcome checked decreasing
  | southEast => exact oracleSound702 p outcome checked decreasing
  | southWest => exact oracleSound703 p outcome checked decreasing
theorem heroSound177 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 177 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 177 p) :
    NetHack.Sokoban22Refined85.bonus 177 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 177 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound704 p outcome checked decreasing
  | south => exact oracleSound705 p outcome checked decreasing
  | east => exact oracleSound706 p outcome checked decreasing
  | west => exact oracleSound707 p outcome checked decreasing
  | northEast => exact oracleSound708 p outcome checked decreasing
  | northWest => exact oracleSound709 p outcome checked decreasing
  | southEast => exact oracleSound710 p outcome checked decreasing
  | southWest => exact oracleSound711 p outcome checked decreasing
theorem heroSound180 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 180 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 180 p) :
    NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 180 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound712 p outcome checked decreasing
  | south => exact oracleSound713 p outcome checked decreasing
  | east => exact oracleSound714 p outcome checked decreasing
  | west => exact oracleSound715 p outcome checked decreasing
  | northEast => exact oracleSound716 p outcome checked decreasing
  | northWest => exact oracleSound717 p outcome checked decreasing
  | southEast => exact oracleSound718 p outcome checked decreasing
  | southWest => exact oracleSound719 p outcome checked decreasing
theorem heroSound181 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound720 p outcome checked decreasing
  | south => exact oracleSound721 p outcome checked decreasing
  | east => exact oracleSound722 p outcome checked decreasing
  | west => exact oracleSound723 p outcome checked decreasing
  | northEast => exact oracleSound724 p outcome checked decreasing
  | northWest => exact oracleSound725 p outcome checked decreasing
  | southEast => exact oracleSound726 p outcome checked decreasing
  | southWest => exact oracleSound727 p outcome checked decreasing
theorem heroSound182 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound728 p outcome checked decreasing
  | south => exact oracleSound729 p outcome checked decreasing
  | east => exact oracleSound730 p outcome checked decreasing
  | west => exact oracleSound731 p outcome checked decreasing
  | northEast => exact oracleSound732 p outcome checked decreasing
  | northWest => exact oracleSound733 p outcome checked decreasing
  | southEast => exact oracleSound734 p outcome checked decreasing
  | southWest => exact oracleSound735 p outcome checked decreasing
theorem heroSound184 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound736 p outcome checked decreasing
  | south => exact oracleSound737 p outcome checked decreasing
  | east => exact oracleSound738 p outcome checked decreasing
  | west => exact oracleSound739 p outcome checked decreasing
  | northEast => exact oracleSound740 p outcome checked decreasing
  | northWest => exact oracleSound741 p outcome checked decreasing
  | southEast => exact oracleSound742 p outcome checked decreasing
  | southWest => exact oracleSound743 p outcome checked decreasing
theorem heroSound185 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound744 p outcome checked decreasing
  | south => exact oracleSound745 p outcome checked decreasing
  | east => exact oracleSound746 p outcome checked decreasing
  | west => exact oracleSound747 p outcome checked decreasing
  | northEast => exact oracleSound748 p outcome checked decreasing
  | northWest => exact oracleSound749 p outcome checked decreasing
  | southEast => exact oracleSound750 p outcome checked decreasing
  | southWest => exact oracleSound751 p outcome checked decreasing
theorem heroSound186 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound752 p outcome checked decreasing
  | south => exact oracleSound753 p outcome checked decreasing
  | east => exact oracleSound754 p outcome checked decreasing
  | west => exact oracleSound755 p outcome checked decreasing
  | northEast => exact oracleSound756 p outcome checked decreasing
  | northWest => exact oracleSound757 p outcome checked decreasing
  | southEast => exact oracleSound758 p outcome checked decreasing
  | southWest => exact oracleSound759 p outcome checked decreasing
theorem heroSound188 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound760 p outcome checked decreasing
  | south => exact oracleSound761 p outcome checked decreasing
  | east => exact oracleSound762 p outcome checked decreasing
  | west => exact oracleSound763 p outcome checked decreasing
  | northEast => exact oracleSound764 p outcome checked decreasing
  | northWest => exact oracleSound765 p outcome checked decreasing
  | southEast => exact oracleSound766 p outcome checked decreasing
  | southWest => exact oracleSound767 p outcome checked decreasing
theorem heroSound189 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound768 p outcome checked decreasing
  | south => exact oracleSound769 p outcome checked decreasing
  | east => exact oracleSound770 p outcome checked decreasing
  | west => exact oracleSound771 p outcome checked decreasing
  | northEast => exact oracleSound772 p outcome checked decreasing
  | northWest => exact oracleSound773 p outcome checked decreasing
  | southEast => exact oracleSound774 p outcome checked decreasing
  | southWest => exact oracleSound775 p outcome checked decreasing
theorem heroSound190 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound776 p outcome checked decreasing
  | south => exact oracleSound777 p outcome checked decreasing
  | east => exact oracleSound778 p outcome checked decreasing
  | west => exact oracleSound779 p outcome checked decreasing
  | northEast => exact oracleSound780 p outcome checked decreasing
  | northWest => exact oracleSound781 p outcome checked decreasing
  | southEast => exact oracleSound782 p outcome checked decreasing
  | southWest => exact oracleSound783 p outcome checked decreasing
theorem heroSound191 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound784 p outcome checked decreasing
  | south => exact oracleSound785 p outcome checked decreasing
  | east => exact oracleSound786 p outcome checked decreasing
  | west => exact oracleSound787 p outcome checked decreasing
  | northEast => exact oracleSound788 p outcome checked decreasing
  | northWest => exact oracleSound789 p outcome checked decreasing
  | southEast => exact oracleSound790 p outcome checked decreasing
  | southWest => exact oracleSound791 p outcome checked decreasing
theorem heroSound192 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound792 p outcome checked decreasing
  | south => exact oracleSound793 p outcome checked decreasing
  | east => exact oracleSound794 p outcome checked decreasing
  | west => exact oracleSound795 p outcome checked decreasing
  | northEast => exact oracleSound796 p outcome checked decreasing
  | northWest => exact oracleSound797 p outcome checked decreasing
  | southEast => exact oracleSound798 p outcome checked decreasing
  | southWest => exact oracleSound799 p outcome checked decreasing
theorem heroSound193 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound800 p outcome checked decreasing
  | south => exact oracleSound801 p outcome checked decreasing
  | east => exact oracleSound802 p outcome checked decreasing
  | west => exact oracleSound803 p outcome checked decreasing
  | northEast => exact oracleSound804 p outcome checked decreasing
  | northWest => exact oracleSound805 p outcome checked decreasing
  | southEast => exact oracleSound806 p outcome checked decreasing
  | southWest => exact oracleSound807 p outcome checked decreasing
theorem heroSound194 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound808 p outcome checked decreasing
  | south => exact oracleSound809 p outcome checked decreasing
  | east => exact oracleSound810 p outcome checked decreasing
  | west => exact oracleSound811 p outcome checked decreasing
  | northEast => exact oracleSound812 p outcome checked decreasing
  | northWest => exact oracleSound813 p outcome checked decreasing
  | southEast => exact oracleSound814 p outcome checked decreasing
  | southWest => exact oracleSound815 p outcome checked decreasing
theorem heroSound199 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound816 p outcome checked decreasing
  | south => exact oracleSound817 p outcome checked decreasing
  | east => exact oracleSound818 p outcome checked decreasing
  | west => exact oracleSound819 p outcome checked decreasing
  | northEast => exact oracleSound820 p outcome checked decreasing
  | northWest => exact oracleSound821 p outcome checked decreasing
  | southEast => exact oracleSound822 p outcome checked decreasing
  | southWest => exact oracleSound823 p outcome checked decreasing
theorem heroSound200 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound824 p outcome checked decreasing
  | south => exact oracleSound825 p outcome checked decreasing
  | east => exact oracleSound826 p outcome checked decreasing
  | west => exact oracleSound827 p outcome checked decreasing
  | northEast => exact oracleSound828 p outcome checked decreasing
  | northWest => exact oracleSound829 p outcome checked decreasing
  | southEast => exact oracleSound830 p outcome checked decreasing
  | southWest => exact oracleSound831 p outcome checked decreasing
theorem heroSound201 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound832 p outcome checked decreasing
  | south => exact oracleSound833 p outcome checked decreasing
  | east => exact oracleSound834 p outcome checked decreasing
  | west => exact oracleSound835 p outcome checked decreasing
  | northEast => exact oracleSound836 p outcome checked decreasing
  | northWest => exact oracleSound837 p outcome checked decreasing
  | southEast => exact oracleSound838 p outcome checked decreasing
  | southWest => exact oracleSound839 p outcome checked decreasing
theorem heroSound202 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound840 p outcome checked decreasing
  | south => exact oracleSound841 p outcome checked decreasing
  | east => exact oracleSound842 p outcome checked decreasing
  | west => exact oracleSound843 p outcome checked decreasing
  | northEast => exact oracleSound844 p outcome checked decreasing
  | northWest => exact oracleSound845 p outcome checked decreasing
  | southEast => exact oracleSound846 p outcome checked decreasing
  | southWest => exact oracleSound847 p outcome checked decreasing
theorem heroSound204 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound848 p outcome checked decreasing
  | south => exact oracleSound849 p outcome checked decreasing
  | east => exact oracleSound850 p outcome checked decreasing
  | west => exact oracleSound851 p outcome checked decreasing
  | northEast => exact oracleSound852 p outcome checked decreasing
  | northWest => exact oracleSound853 p outcome checked decreasing
  | southEast => exact oracleSound854 p outcome checked decreasing
  | southWest => exact oracleSound855 p outcome checked decreasing
theorem heroSound210 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound856 p outcome checked decreasing
  | south => exact oracleSound857 p outcome checked decreasing
  | east => exact oracleSound858 p outcome checked decreasing
  | west => exact oracleSound859 p outcome checked decreasing
  | northEast => exact oracleSound860 p outcome checked decreasing
  | northWest => exact oracleSound861 p outcome checked decreasing
  | southEast => exact oracleSound862 p outcome checked decreasing
  | southWest => exact oracleSound863 p outcome checked decreasing
theorem heroSound211 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound864 p outcome checked decreasing
  | south => exact oracleSound865 p outcome checked decreasing
  | east => exact oracleSound866 p outcome checked decreasing
  | west => exact oracleSound867 p outcome checked decreasing
  | northEast => exact oracleSound868 p outcome checked decreasing
  | northWest => exact oracleSound869 p outcome checked decreasing
  | southEast => exact oracleSound870 p outcome checked decreasing
  | southWest => exact oracleSound871 p outcome checked decreasing
theorem heroSound212 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound872 p outcome checked decreasing
  | south => exact oracleSound873 p outcome checked decreasing
  | east => exact oracleSound874 p outcome checked decreasing
  | west => exact oracleSound875 p outcome checked decreasing
  | northEast => exact oracleSound876 p outcome checked decreasing
  | northWest => exact oracleSound877 p outcome checked decreasing
  | southEast => exact oracleSound878 p outcome checked decreasing
  | southWest => exact oracleSound879 p outcome checked decreasing
theorem heroSound213 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 213 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 213 p) :
    NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 213 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound880 p outcome checked decreasing
  | south => exact oracleSound881 p outcome checked decreasing
  | east => exact oracleSound882 p outcome checked decreasing
  | west => exact oracleSound883 p outcome checked decreasing
  | northEast => exact oracleSound884 p outcome checked decreasing
  | northWest => exact oracleSound885 p outcome checked decreasing
  | southEast => exact oracleSound886 p outcome checked decreasing
  | southWest => exact oracleSound887 p outcome checked decreasing
theorem heroSound214 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 214 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 214 p) :
    NetHack.Sokoban22Refined85.bonus 214 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 214 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound888 p outcome checked decreasing
  | south => exact oracleSound889 p outcome checked decreasing
  | east => exact oracleSound890 p outcome checked decreasing
  | west => exact oracleSound891 p outcome checked decreasing
  | northEast => exact oracleSound892 p outcome checked decreasing
  | northWest => exact oracleSound893 p outcome checked decreasing
  | southEast => exact oracleSound894 p outcome checked decreasing
  | southWest => exact oracleSound895 p outcome checked decreasing
theorem heroSound215 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 215 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 215 p) :
    NetHack.Sokoban22Refined85.bonus 215 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 215 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound896 p outcome checked decreasing
  | south => exact oracleSound897 p outcome checked decreasing
  | east => exact oracleSound898 p outcome checked decreasing
  | west => exact oracleSound899 p outcome checked decreasing
  | northEast => exact oracleSound900 p outcome checked decreasing
  | northWest => exact oracleSound901 p outcome checked decreasing
  | southEast => exact oracleSound902 p outcome checked decreasing
  | southWest => exact oracleSound903 p outcome checked decreasing
theorem heroSound216 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 216 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 216 p) :
    NetHack.Sokoban22Refined85.bonus 216 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 216 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound904 p outcome checked decreasing
  | south => exact oracleSound905 p outcome checked decreasing
  | east => exact oracleSound906 p outcome checked decreasing
  | west => exact oracleSound907 p outcome checked decreasing
  | northEast => exact oracleSound908 p outcome checked decreasing
  | northWest => exact oracleSound909 p outcome checked decreasing
  | southEast => exact oracleSound910 p outcome checked decreasing
  | southWest => exact oracleSound911 p outcome checked decreasing
theorem heroSound218 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 218 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 218 p) :
    NetHack.Sokoban22Refined85.bonus 218 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 218 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound912 p outcome checked decreasing
  | south => exact oracleSound913 p outcome checked decreasing
  | east => exact oracleSound914 p outcome checked decreasing
  | west => exact oracleSound915 p outcome checked decreasing
  | northEast => exact oracleSound916 p outcome checked decreasing
  | northWest => exact oracleSound917 p outcome checked decreasing
  | southEast => exact oracleSound918 p outcome checked decreasing
  | southWest => exact oracleSound919 p outcome checked decreasing
theorem heroSound223 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 223 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 223 p) :
    NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 223 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound920 p outcome checked decreasing
  | south => exact oracleSound921 p outcome checked decreasing
  | east => exact oracleSound922 p outcome checked decreasing
  | west => exact oracleSound923 p outcome checked decreasing
  | northEast => exact oracleSound924 p outcome checked decreasing
  | northWest => exact oracleSound925 p outcome checked decreasing
  | southEast => exact oracleSound926 p outcome checked decreasing
  | southWest => exact oracleSound927 p outcome checked decreasing
theorem heroSound224 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 224 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 224 p) :
    NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 224 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound928 p outcome checked decreasing
  | south => exact oracleSound929 p outcome checked decreasing
  | east => exact oracleSound930 p outcome checked decreasing
  | west => exact oracleSound931 p outcome checked decreasing
  | northEast => exact oracleSound932 p outcome checked decreasing
  | northWest => exact oracleSound933 p outcome checked decreasing
  | southEast => exact oracleSound934 p outcome checked decreasing
  | southWest => exact oracleSound935 p outcome checked decreasing
theorem heroSound225 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 225 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 225 p) :
    NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 225 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound936 p outcome checked decreasing
  | south => exact oracleSound937 p outcome checked decreasing
  | east => exact oracleSound938 p outcome checked decreasing
  | west => exact oracleSound939 p outcome checked decreasing
  | northEast => exact oracleSound940 p outcome checked decreasing
  | northWest => exact oracleSound941 p outcome checked decreasing
  | southEast => exact oracleSound942 p outcome checked decreasing
  | southWest => exact oracleSound943 p outcome checked decreasing
theorem heroSound226 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 226 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 226 p) :
    NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 226 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound944 p outcome checked decreasing
  | south => exact oracleSound945 p outcome checked decreasing
  | east => exact oracleSound946 p outcome checked decreasing
  | west => exact oracleSound947 p outcome checked decreasing
  | northEast => exact oracleSound948 p outcome checked decreasing
  | northWest => exact oracleSound949 p outcome checked decreasing
  | southEast => exact oracleSound950 p outcome checked decreasing
  | southWest => exact oracleSound951 p outcome checked decreasing
theorem heroSound240 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 240 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 240 p) :
    NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 240 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound952 p outcome checked decreasing
  | south => exact oracleSound953 p outcome checked decreasing
  | east => exact oracleSound954 p outcome checked decreasing
  | west => exact oracleSound955 p outcome checked decreasing
  | northEast => exact oracleSound956 p outcome checked decreasing
  | northWest => exact oracleSound957 p outcome checked decreasing
  | southEast => exact oracleSound958 p outcome checked decreasing
  | southWest => exact oracleSound959 p outcome checked decreasing
theorem heroSound245 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 245 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 245 p) :
    NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 245 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound960 p outcome checked decreasing
  | south => exact oracleSound961 p outcome checked decreasing
  | east => exact oracleSound962 p outcome checked decreasing
  | west => exact oracleSound963 p outcome checked decreasing
  | northEast => exact oracleSound964 p outcome checked decreasing
  | northWest => exact oracleSound965 p outcome checked decreasing
  | southEast => exact oracleSound966 p outcome checked decreasing
  | southWest => exact oracleSound967 p outcome checked decreasing
theorem heroSound246 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 246 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 246 p) :
    NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 246 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound968 p outcome checked decreasing
  | south => exact oracleSound969 p outcome checked decreasing
  | east => exact oracleSound970 p outcome checked decreasing
  | west => exact oracleSound971 p outcome checked decreasing
  | northEast => exact oracleSound972 p outcome checked decreasing
  | northWest => exact oracleSound973 p outcome checked decreasing
  | southEast => exact oracleSound974 p outcome checked decreasing
  | southWest => exact oracleSound975 p outcome checked decreasing
theorem heroSound247 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 247 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 247 p) :
    NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 247 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound976 p outcome checked decreasing
  | south => exact oracleSound977 p outcome checked decreasing
  | east => exact oracleSound978 p outcome checked decreasing
  | west => exact oracleSound979 p outcome checked decreasing
  | northEast => exact oracleSound980 p outcome checked decreasing
  | northWest => exact oracleSound981 p outcome checked decreasing
  | southEast => exact oracleSound982 p outcome checked decreasing
  | southWest => exact oracleSound983 p outcome checked decreasing
theorem heroSound248 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 248 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 248 p) :
    NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 248 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound984 p outcome checked decreasing
  | south => exact oracleSound985 p outcome checked decreasing
  | east => exact oracleSound986 p outcome checked decreasing
  | west => exact oracleSound987 p outcome checked decreasing
  | northEast => exact oracleSound988 p outcome checked decreasing
  | northWest => exact oracleSound989 p outcome checked decreasing
  | southEast => exact oracleSound990 p outcome checked decreasing
  | southWest => exact oracleSound991 p outcome checked decreasing
theorem heroSound249 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 249 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 249 p) :
    NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 249 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound992 p outcome checked decreasing
  | south => exact oracleSound993 p outcome checked decreasing
  | east => exact oracleSound994 p outcome checked decreasing
  | west => exact oracleSound995 p outcome checked decreasing
  | northEast => exact oracleSound996 p outcome checked decreasing
  | northWest => exact oracleSound997 p outcome checked decreasing
  | southEast => exact oracleSound998 p outcome checked decreasing
  | southWest => exact oracleSound999 p outcome checked decreasing
theorem heroSound250 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 250 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 250 p) :
    NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 250 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1000 p outcome checked decreasing
  | south => exact oracleSound1001 p outcome checked decreasing
  | east => exact oracleSound1002 p outcome checked decreasing
  | west => exact oracleSound1003 p outcome checked decreasing
  | northEast => exact oracleSound1004 p outcome checked decreasing
  | northWest => exact oracleSound1005 p outcome checked decreasing
  | southEast => exact oracleSound1006 p outcome checked decreasing
  | southWest => exact oracleSound1007 p outcome checked decreasing
theorem heroSound251 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 251 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 251 p) :
    NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 251 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1008 p outcome checked decreasing
  | south => exact oracleSound1009 p outcome checked decreasing
  | east => exact oracleSound1010 p outcome checked decreasing
  | west => exact oracleSound1011 p outcome checked decreasing
  | northEast => exact oracleSound1012 p outcome checked decreasing
  | northWest => exact oracleSound1013 p outcome checked decreasing
  | southEast => exact oracleSound1014 p outcome checked decreasing
  | southWest => exact oracleSound1015 p outcome checked decreasing
theorem heroSound252 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 252 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 252 p) :
    NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 252 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1016 p outcome checked decreasing
  | south => exact oracleSound1017 p outcome checked decreasing
  | east => exact oracleSound1018 p outcome checked decreasing
  | west => exact oracleSound1019 p outcome checked decreasing
  | northEast => exact oracleSound1020 p outcome checked decreasing
  | northWest => exact oracleSound1021 p outcome checked decreasing
  | southEast => exact oracleSound1022 p outcome checked decreasing
  | southWest => exact oracleSound1023 p outcome checked decreasing
theorem heroSound253 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 253 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 253 p) :
    NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 253 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1024 p outcome checked decreasing
  | south => exact oracleSound1025 p outcome checked decreasing
  | east => exact oracleSound1026 p outcome checked decreasing
  | west => exact oracleSound1027 p outcome checked decreasing
  | northEast => exact oracleSound1028 p outcome checked decreasing
  | northWest => exact oracleSound1029 p outcome checked decreasing
  | southEast => exact oracleSound1030 p outcome checked decreasing
  | southWest => exact oracleSound1031 p outcome checked decreasing
theorem heroSound254 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 254 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 254 p) :
    NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 254 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1032 p outcome checked decreasing
  | south => exact oracleSound1033 p outcome checked decreasing
  | east => exact oracleSound1034 p outcome checked decreasing
  | west => exact oracleSound1035 p outcome checked decreasing
  | northEast => exact oracleSound1036 p outcome checked decreasing
  | northWest => exact oracleSound1037 p outcome checked decreasing
  | southEast => exact oracleSound1038 p outcome checked decreasing
  | southWest => exact oracleSound1039 p outcome checked decreasing
theorem heroSound255 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 255 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 255 p) :
    NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 255 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1040 p outcome checked decreasing
  | south => exact oracleSound1041 p outcome checked decreasing
  | east => exact oracleSound1042 p outcome checked decreasing
  | west => exact oracleSound1043 p outcome checked decreasing
  | northEast => exact oracleSound1044 p outcome checked decreasing
  | northWest => exact oracleSound1045 p outcome checked decreasing
  | southEast => exact oracleSound1046 p outcome checked decreasing
  | southWest => exact oracleSound1047 p outcome checked decreasing
theorem heroSound256 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 256 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 256 p) :
    NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 256 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1048 p outcome checked decreasing
  | south => exact oracleSound1049 p outcome checked decreasing
  | east => exact oracleSound1050 p outcome checked decreasing
  | west => exact oracleSound1051 p outcome checked decreasing
  | northEast => exact oracleSound1052 p outcome checked decreasing
  | northWest => exact oracleSound1053 p outcome checked decreasing
  | southEast => exact oracleSound1054 p outcome checked decreasing
  | southWest => exact oracleSound1055 p outcome checked decreasing
theorem heroSound257 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 257 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 257 p) :
    NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 257 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1056 p outcome checked decreasing
  | south => exact oracleSound1057 p outcome checked decreasing
  | east => exact oracleSound1058 p outcome checked decreasing
  | west => exact oracleSound1059 p outcome checked decreasing
  | northEast => exact oracleSound1060 p outcome checked decreasing
  | northWest => exact oracleSound1061 p outcome checked decreasing
  | southEast => exact oracleSound1062 p outcome checked decreasing
  | southWest => exact oracleSound1063 p outcome checked decreasing
theorem heroSound258 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 258 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 258 p) :
    NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 258 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1064 p outcome checked decreasing
  | south => exact oracleSound1065 p outcome checked decreasing
  | east => exact oracleSound1066 p outcome checked decreasing
  | west => exact oracleSound1067 p outcome checked decreasing
  | northEast => exact oracleSound1068 p outcome checked decreasing
  | northWest => exact oracleSound1069 p outcome checked decreasing
  | southEast => exact oracleSound1070 p outcome checked decreasing
  | southWest => exact oracleSound1071 p outcome checked decreasing
theorem heroSound259 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 259 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 259 p) :
    NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 259 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1072 p outcome checked decreasing
  | south => exact oracleSound1073 p outcome checked decreasing
  | east => exact oracleSound1074 p outcome checked decreasing
  | west => exact oracleSound1075 p outcome checked decreasing
  | northEast => exact oracleSound1076 p outcome checked decreasing
  | northWest => exact oracleSound1077 p outcome checked decreasing
  | southEast => exact oracleSound1078 p outcome checked decreasing
  | southWest => exact oracleSound1079 p outcome checked decreasing
theorem heroSound260 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 260 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 260 p) :
    NetHack.Sokoban22Refined85.bonus 260 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 260 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1080 p outcome checked decreasing
  | south => exact oracleSound1081 p outcome checked decreasing
  | east => exact oracleSound1082 p outcome checked decreasing
  | west => exact oracleSound1083 p outcome checked decreasing
  | northEast => exact oracleSound1084 p outcome checked decreasing
  | northWest => exact oracleSound1085 p outcome checked decreasing
  | southEast => exact oracleSound1086 p outcome checked decreasing
  | southWest => exact oracleSound1087 p outcome checked decreasing
theorem heroSound262 (direction : Dir) (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 262 direction = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 262 p) :
    NetHack.Sokoban22Refined85.bonus 262 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 262 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  cases direction with
  | north => exact oracleSound1088 p outcome checked decreasing
  | south => exact oracleSound1089 p outcome checked decreasing
  | east => exact oracleSound1090 p outcome checked decreasing
  | west => exact oracleSound1091 p outcome checked decreasing
  | northEast => exact oracleSound1092 p outcome checked decreasing
  | northWest => exact oracleSound1093 p outcome checked decreasing
  | southEast => exact oracleSound1094 p outcome checked decreasing
  | southWest => exact oracleSound1095 p outcome checked decreasing
end NetHack.Soko22Hazard87
