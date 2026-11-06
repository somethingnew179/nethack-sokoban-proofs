import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1728_0_checked : (List.range' 884736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1728_1_checked : (List.range' 884864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1728_2_checked : (List.range' 884992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1728_3_checked : (List.range' 885120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1728_range (index : Nat) (lower : 884736 ≤ index) (upper : index < 885248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 884992 then
    if cut : index < 884864 then
      exact segment_sound _ 884736 128 Restriction1728_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 884864 128 Restriction1728_1_checked index (by omega) (by omega)
  else
    if cut : index < 885120 then
      exact segment_sound _ 884992 128 Restriction1728_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 885120 128 Restriction1728_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
