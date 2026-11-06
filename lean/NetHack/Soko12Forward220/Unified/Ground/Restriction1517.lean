import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1517_0_checked : (List.range' 776704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1517_1_checked : (List.range' 776832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1517_2_checked : (List.range' 776960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1517_3_checked : (List.range' 777088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1517_range (index : Nat) (lower : 776704 ≤ index) (upper : index < 777216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 776960 then
    if cut : index < 776832 then
      exact segment_sound _ 776704 128 Restriction1517_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 776832 128 Restriction1517_1_checked index (by omega) (by omega)
  else
    if cut : index < 777088 then
      exact segment_sound _ 776960 128 Restriction1517_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 777088 128 Restriction1517_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
