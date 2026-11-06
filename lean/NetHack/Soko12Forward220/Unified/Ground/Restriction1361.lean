import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1361_0_checked : (List.range' 696832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1361_1_checked : (List.range' 696960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1361_2_checked : (List.range' 697088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1361_3_checked : (List.range' 697216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1361_range (index : Nat) (lower : 696832 ≤ index) (upper : index < 697344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 697088 then
    if cut : index < 696960 then
      exact segment_sound _ 696832 128 Restriction1361_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 696960 128 Restriction1361_1_checked index (by omega) (by omega)
  else
    if cut : index < 697216 then
      exact segment_sound _ 697088 128 Restriction1361_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 697216 128 Restriction1361_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
