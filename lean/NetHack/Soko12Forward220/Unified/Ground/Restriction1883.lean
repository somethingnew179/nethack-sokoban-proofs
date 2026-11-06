import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1883_0_checked : (List.range' 964096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1883_1_checked : (List.range' 964224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1883_2_checked : (List.range' 964352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1883_3_checked : (List.range' 964480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1883_range (index : Nat) (lower : 964096 ≤ index) (upper : index < 964608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 964352 then
    if cut : index < 964224 then
      exact segment_sound _ 964096 128 Restriction1883_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 964224 128 Restriction1883_1_checked index (by omega) (by omega)
  else
    if cut : index < 964480 then
      exact segment_sound _ 964352 128 Restriction1883_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 964480 128 Restriction1883_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
