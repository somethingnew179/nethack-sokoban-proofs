import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2543_0_checked : (List.range' 1302016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2543_1_checked : (List.range' 1302144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2543_2_checked : (List.range' 1302272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2543_3_checked : (List.range' 1302400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2543_range (index : Nat) (lower : 1302016 ≤ index) (upper : index < 1302528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1302272 then
    if cut : index < 1302144 then
      exact segment_sound _ 1302016 128 Restriction2543_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1302144 128 Restriction2543_1_checked index (by omega) (by omega)
  else
    if cut : index < 1302400 then
      exact segment_sound _ 1302272 128 Restriction2543_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1302400 128 Restriction2543_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
