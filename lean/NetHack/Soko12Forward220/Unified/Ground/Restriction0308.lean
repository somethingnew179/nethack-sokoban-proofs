import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0308_0_checked : (List.range' 157696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0308_1_checked : (List.range' 157824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0308_2_checked : (List.range' 157952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0308_3_checked : (List.range' 158080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0308_range (index : Nat) (lower : 157696 ≤ index) (upper : index < 158208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 157952 then
    if cut : index < 157824 then
      exact segment_sound _ 157696 128 Restriction0308_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 157824 128 Restriction0308_1_checked index (by omega) (by omega)
  else
    if cut : index < 158080 then
      exact segment_sound _ 157952 128 Restriction0308_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 158080 128 Restriction0308_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
