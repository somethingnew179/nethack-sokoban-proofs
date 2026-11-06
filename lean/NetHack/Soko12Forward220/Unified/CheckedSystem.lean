import NetHack.Soko12Forward220.Unified.RawData
import NetHack.Soko12Forward220.Unified.CheckedUpdate
import NetHack.Soko12Forward220.Unified.CheckedRestriction
import NetHack.Soko12Forward220.Unified.CheckedNumeric
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified
open NetHack.Sokoban
noncomputable def checkedSystem : CountedLocalCase.System where
  read := read
  support := cells
  updates := updates
  updateCount := updateCount
  updatesValid := updates_sound
  restrictions := restrictions
  restrictionCount := restrictionCount
  restrictionsValid := restrictions_sound
  numeric := numeric
  numericCount := numericCount
  numericValid := numeric_sound
theorem checkedSystem_data : CountedLocalCaseData.fromSystem checkedSystem = data := rfl
end NetHack.Soko12Forward220.Unified
