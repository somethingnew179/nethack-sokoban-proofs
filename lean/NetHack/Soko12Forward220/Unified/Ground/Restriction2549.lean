import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2549_0_checked : (List.range' 1305088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2549_1_checked : (List.range' 1305216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2549_2_checked : (List.range' 1305344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2549_3_checked : (List.range' 1305472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2549_range (index : Nat) (lower : 1305088 ≤ index) (upper : index < 1305600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1305344 then
    if cut : index < 1305216 then
      exact segment_sound _ 1305088 128 Restriction2549_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1305216 128 Restriction2549_1_checked index (by omega) (by omega)
  else
    if cut : index < 1305472 then
      exact segment_sound _ 1305344 128 Restriction2549_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1305472 128 Restriction2549_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
