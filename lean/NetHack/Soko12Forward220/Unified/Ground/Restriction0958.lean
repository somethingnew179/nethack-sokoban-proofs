import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0958_0_checked : (List.range' 490496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0958_1_checked : (List.range' 490624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0958_2_checked : (List.range' 490752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0958_3_checked : (List.range' 490880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0958_range (index : Nat) (lower : 490496 ≤ index) (upper : index < 491008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 490752 then
    if cut : index < 490624 then
      exact segment_sound _ 490496 128 Restriction0958_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 490624 128 Restriction0958_1_checked index (by omega) (by omega)
  else
    if cut : index < 490880 then
      exact segment_sound _ 490752 128 Restriction0958_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 490880 128 Restriction0958_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
