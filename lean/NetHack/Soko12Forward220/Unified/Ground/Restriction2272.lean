import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2272_0_checked : (List.range' 1163264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2272_1_checked : (List.range' 1163392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2272_2_checked : (List.range' 1163520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2272_3_checked : (List.range' 1163648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2272_range (index : Nat) (lower : 1163264 ≤ index) (upper : index < 1163776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1163520 then
    if cut : index < 1163392 then
      exact segment_sound _ 1163264 128 Restriction2272_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1163392 128 Restriction2272_1_checked index (by omega) (by omega)
  else
    if cut : index < 1163648 then
      exact segment_sound _ 1163520 128 Restriction2272_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1163648 128 Restriction2272_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
