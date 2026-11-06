import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2109_0_checked : (List.range' 1079808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2109_1_checked : (List.range' 1079936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2109_2_checked : (List.range' 1080064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2109_3_checked : (List.range' 1080192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2109_range (index : Nat) (lower : 1079808 ≤ index) (upper : index < 1080320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1080064 then
    if cut : index < 1079936 then
      exact segment_sound _ 1079808 128 Restriction2109_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1079936 128 Restriction2109_1_checked index (by omega) (by omega)
  else
    if cut : index < 1080192 then
      exact segment_sound _ 1080064 128 Restriction2109_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1080192 128 Restriction2109_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
