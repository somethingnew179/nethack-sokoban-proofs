import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2529_0_checked : (List.range' 1294848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2529_1_checked : (List.range' 1294976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2529_2_checked : (List.range' 1295104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2529_3_checked : (List.range' 1295232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2529_range (index : Nat) (lower : 1294848 ≤ index) (upper : index < 1295360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1295104 then
    if cut : index < 1294976 then
      exact segment_sound _ 1294848 128 Restriction2529_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1294976 128 Restriction2529_1_checked index (by omega) (by omega)
  else
    if cut : index < 1295232 then
      exact segment_sound _ 1295104 128 Restriction2529_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1295232 128 Restriction2529_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
