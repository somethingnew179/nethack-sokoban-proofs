import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2319_0_checked : (List.range' 1187328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2319_1_checked : (List.range' 1187456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2319_2_checked : (List.range' 1187584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2319_3_checked : (List.range' 1187712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2319_range (index : Nat) (lower : 1187328 ≤ index) (upper : index < 1187840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1187584 then
    if cut : index < 1187456 then
      exact segment_sound _ 1187328 128 Restriction2319_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1187456 128 Restriction2319_1_checked index (by omega) (by omega)
  else
    if cut : index < 1187712 then
      exact segment_sound _ 1187584 128 Restriction2319_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1187712 128 Restriction2319_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
