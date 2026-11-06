import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1084_0_checked : (List.range' 555008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1084_1_checked : (List.range' 555136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1084_2_checked : (List.range' 555264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1084_3_checked : (List.range' 555392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1084_range (index : Nat) (lower : 555008 ≤ index) (upper : index < 555520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 555264 then
    if cut : index < 555136 then
      exact segment_sound _ 555008 128 Restriction1084_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 555136 128 Restriction1084_1_checked index (by omega) (by omega)
  else
    if cut : index < 555392 then
      exact segment_sound _ 555264 128 Restriction1084_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 555392 128 Restriction1084_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
