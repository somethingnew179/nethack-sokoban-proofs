import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2003_0_checked : (List.range' 1025536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2003_1_checked : (List.range' 1025664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2003_2_checked : (List.range' 1025792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2003_3_checked : (List.range' 1025920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2003_range (index : Nat) (lower : 1025536 ≤ index) (upper : index < 1026048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1025792 then
    if cut : index < 1025664 then
      exact segment_sound _ 1025536 128 Restriction2003_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1025664 128 Restriction2003_1_checked index (by omega) (by omega)
  else
    if cut : index < 1025920 then
      exact segment_sound _ 1025792 128 Restriction2003_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1025920 128 Restriction2003_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
