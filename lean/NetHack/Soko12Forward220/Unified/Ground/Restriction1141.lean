import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1141_0_checked : (List.range' 584192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1141_1_checked : (List.range' 584320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1141_2_checked : (List.range' 584448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1141_3_checked : (List.range' 584576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1141_range (index : Nat) (lower : 584192 ≤ index) (upper : index < 584704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 584448 then
    if cut : index < 584320 then
      exact segment_sound _ 584192 128 Restriction1141_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 584320 128 Restriction1141_1_checked index (by omega) (by omega)
  else
    if cut : index < 584576 then
      exact segment_sound _ 584448 128 Restriction1141_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 584576 128 Restriction1141_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
