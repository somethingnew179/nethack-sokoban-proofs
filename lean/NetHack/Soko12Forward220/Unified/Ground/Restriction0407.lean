import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0407_0_checked : (List.range' 208384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0407_1_checked : (List.range' 208512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0407_2_checked : (List.range' 208640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0407_3_checked : (List.range' 208768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0407_range (index : Nat) (lower : 208384 ≤ index) (upper : index < 208896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 208640 then
    if cut : index < 208512 then
      exact segment_sound _ 208384 128 Restriction0407_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 208512 128 Restriction0407_1_checked index (by omega) (by omega)
  else
    if cut : index < 208768 then
      exact segment_sound _ 208640 128 Restriction0407_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 208768 128 Restriction0407_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
