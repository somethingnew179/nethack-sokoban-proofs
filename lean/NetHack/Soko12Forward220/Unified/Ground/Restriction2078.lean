import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2078_0_checked : (List.range' 1063936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2078_1_checked : (List.range' 1064064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2078_2_checked : (List.range' 1064192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2078_3_checked : (List.range' 1064320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2078_range (index : Nat) (lower : 1063936 ≤ index) (upper : index < 1064448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1064192 then
    if cut : index < 1064064 then
      exact segment_sound _ 1063936 128 Restriction2078_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1064064 128 Restriction2078_1_checked index (by omega) (by omega)
  else
    if cut : index < 1064320 then
      exact segment_sound _ 1064192 128 Restriction2078_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1064320 128 Restriction2078_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
