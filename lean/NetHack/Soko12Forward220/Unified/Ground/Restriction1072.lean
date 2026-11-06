import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1072_0_checked : (List.range' 548864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1072_1_checked : (List.range' 548992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1072_2_checked : (List.range' 549120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1072_3_checked : (List.range' 549248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1072_range (index : Nat) (lower : 548864 ≤ index) (upper : index < 549376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 549120 then
    if cut : index < 548992 then
      exact segment_sound _ 548864 128 Restriction1072_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 548992 128 Restriction1072_1_checked index (by omega) (by omega)
  else
    if cut : index < 549248 then
      exact segment_sound _ 549120 128 Restriction1072_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 549248 128 Restriction1072_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
