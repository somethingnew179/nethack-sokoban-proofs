import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0436_0_checked : (List.range' 223232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0436_1_checked : (List.range' 223360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0436_2_checked : (List.range' 223488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0436_3_checked : (List.range' 223616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0436_range (index : Nat) (lower : 223232 ≤ index) (upper : index < 223744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 223488 then
    if cut : index < 223360 then
      exact segment_sound _ 223232 128 Restriction0436_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 223360 128 Restriction0436_1_checked index (by omega) (by omega)
  else
    if cut : index < 223616 then
      exact segment_sound _ 223488 128 Restriction0436_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 223616 128 Restriction0436_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
