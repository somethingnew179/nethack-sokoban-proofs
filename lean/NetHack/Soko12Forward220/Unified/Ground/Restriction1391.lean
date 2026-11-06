import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1391_0_checked : (List.range' 712192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1391_1_checked : (List.range' 712320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1391_2_checked : (List.range' 712448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1391_3_checked : (List.range' 712576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1391_range (index : Nat) (lower : 712192 ≤ index) (upper : index < 712704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 712448 then
    if cut : index < 712320 then
      exact segment_sound _ 712192 128 Restriction1391_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 712320 128 Restriction1391_1_checked index (by omega) (by omega)
  else
    if cut : index < 712576 then
      exact segment_sound _ 712448 128 Restriction1391_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 712576 128 Restriction1391_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
