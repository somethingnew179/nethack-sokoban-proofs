import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2015_0_checked : (List.range' 1031680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2015_1_checked : (List.range' 1031808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2015_2_checked : (List.range' 1031936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2015_3_checked : (List.range' 1032064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2015_range (index : Nat) (lower : 1031680 ≤ index) (upper : index < 1032192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1031936 then
    if cut : index < 1031808 then
      exact segment_sound _ 1031680 128 Restriction2015_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1031808 128 Restriction2015_1_checked index (by omega) (by omega)
  else
    if cut : index < 1032064 then
      exact segment_sound _ 1031936 128 Restriction2015_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1032064 128 Restriction2015_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
