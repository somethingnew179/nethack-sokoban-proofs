import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2531_0_checked : (List.range' 1295872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2531_1_checked : (List.range' 1296000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2531_2_checked : (List.range' 1296128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2531_3_checked : (List.range' 1296256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2531_range (index : Nat) (lower : 1295872 ≤ index) (upper : index < 1296384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1296128 then
    if cut : index < 1296000 then
      exact segment_sound _ 1295872 128 Restriction2531_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1296000 128 Restriction2531_1_checked index (by omega) (by omega)
  else
    if cut : index < 1296256 then
      exact segment_sound _ 1296128 128 Restriction2531_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1296256 128 Restriction2531_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
