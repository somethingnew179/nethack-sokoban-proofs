import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2236_0_checked : (List.range' 1144832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2236_1_checked : (List.range' 1144960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2236_2_checked : (List.range' 1145088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2236_3_checked : (List.range' 1145216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2236_range (index : Nat) (lower : 1144832 ≤ index) (upper : index < 1145344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1145088 then
    if cut : index < 1144960 then
      exact segment_sound _ 1144832 128 Restriction2236_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1144960 128 Restriction2236_1_checked index (by omega) (by omega)
  else
    if cut : index < 1145216 then
      exact segment_sound _ 1145088 128 Restriction2236_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1145216 128 Restriction2236_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
