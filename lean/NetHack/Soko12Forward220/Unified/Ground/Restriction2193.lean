import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2193_0_checked : (List.range' 1122816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2193_1_checked : (List.range' 1122944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2193_2_checked : (List.range' 1123072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2193_3_checked : (List.range' 1123200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2193_range (index : Nat) (lower : 1122816 ≤ index) (upper : index < 1123328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1123072 then
    if cut : index < 1122944 then
      exact segment_sound _ 1122816 128 Restriction2193_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1122944 128 Restriction2193_1_checked index (by omega) (by omega)
  else
    if cut : index < 1123200 then
      exact segment_sound _ 1123072 128 Restriction2193_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1123200 128 Restriction2193_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
