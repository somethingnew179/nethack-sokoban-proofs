import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1080_0_checked : (List.range' 552960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1080_1_checked : (List.range' 553088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1080_2_checked : (List.range' 553216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1080_3_checked : (List.range' 553344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1080_range (index : Nat) (lower : 552960 ≤ index) (upper : index < 553472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 553216 then
    if cut : index < 553088 then
      exact segment_sound _ 552960 128 Restriction1080_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 553088 128 Restriction1080_1_checked index (by omega) (by omega)
  else
    if cut : index < 553344 then
      exact segment_sound _ 553216 128 Restriction1080_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 553344 128 Restriction1080_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
