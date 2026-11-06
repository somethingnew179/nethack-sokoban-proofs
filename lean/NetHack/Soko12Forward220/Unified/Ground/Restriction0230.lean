import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0230_0_checked : (List.range' 117760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0230_1_checked : (List.range' 117888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0230_2_checked : (List.range' 118016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0230_3_checked : (List.range' 118144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0230_range (index : Nat) (lower : 117760 ≤ index) (upper : index < 118272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 118016 then
    if cut : index < 117888 then
      exact segment_sound _ 117760 128 Restriction0230_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 117888 128 Restriction0230_1_checked index (by omega) (by omega)
  else
    if cut : index < 118144 then
      exact segment_sound _ 118016 128 Restriction0230_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 118144 128 Restriction0230_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
