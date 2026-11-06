import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2207_0_checked : (List.range' 1129984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2207_1_checked : (List.range' 1130112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2207_2_checked : (List.range' 1130240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2207_3_checked : (List.range' 1130368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2207_range (index : Nat) (lower : 1129984 ≤ index) (upper : index < 1130496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1130240 then
    if cut : index < 1130112 then
      exact segment_sound _ 1129984 128 Restriction2207_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1130112 128 Restriction2207_1_checked index (by omega) (by omega)
  else
    if cut : index < 1130368 then
      exact segment_sound _ 1130240 128 Restriction2207_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1130368 128 Restriction2207_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
