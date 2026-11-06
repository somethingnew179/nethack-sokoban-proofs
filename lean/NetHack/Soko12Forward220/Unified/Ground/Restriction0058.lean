import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0058_0_checked : (List.range' 29696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0058_1_checked : (List.range' 29824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0058_2_checked : (List.range' 29952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0058_3_checked : (List.range' 30080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0058_range (index : Nat) (lower : 29696 ≤ index) (upper : index < 30208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 29952 then
    if cut : index < 29824 then
      exact segment_sound _ 29696 128 Restriction0058_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 29824 128 Restriction0058_1_checked index (by omega) (by omega)
  else
    if cut : index < 30080 then
      exact segment_sound _ 29952 128 Restriction0058_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 30080 128 Restriction0058_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
