import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1219_0_checked : (List.range' 624128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1219_1_checked : (List.range' 624256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1219_2_checked : (List.range' 624384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1219_3_checked : (List.range' 624512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1219_range (index : Nat) (lower : 624128 ≤ index) (upper : index < 624640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 624384 then
    if cut : index < 624256 then
      exact segment_sound _ 624128 128 Restriction1219_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 624256 128 Restriction1219_1_checked index (by omega) (by omega)
  else
    if cut : index < 624512 then
      exact segment_sound _ 624384 128 Restriction1219_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 624512 128 Restriction1219_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
