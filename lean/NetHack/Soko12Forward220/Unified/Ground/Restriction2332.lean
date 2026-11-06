import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2332_0_checked : (List.range' 1193984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2332_1_checked : (List.range' 1194112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2332_2_checked : (List.range' 1194240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2332_3_checked : (List.range' 1194368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2332_range (index : Nat) (lower : 1193984 ≤ index) (upper : index < 1194496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1194240 then
    if cut : index < 1194112 then
      exact segment_sound _ 1193984 128 Restriction2332_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1194112 128 Restriction2332_1_checked index (by omega) (by omega)
  else
    if cut : index < 1194368 then
      exact segment_sound _ 1194240 128 Restriction2332_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1194368 128 Restriction2332_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
