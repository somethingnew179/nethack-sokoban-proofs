import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2256_0_checked : (List.range' 1155072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2256_1_checked : (List.range' 1155200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2256_2_checked : (List.range' 1155328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2256_3_checked : (List.range' 1155456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2256_range (index : Nat) (lower : 1155072 ≤ index) (upper : index < 1155584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1155328 then
    if cut : index < 1155200 then
      exact segment_sound _ 1155072 128 Restriction2256_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1155200 128 Restriction2256_1_checked index (by omega) (by omega)
  else
    if cut : index < 1155456 then
      exact segment_sound _ 1155328 128 Restriction2256_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1155456 128 Restriction2256_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
