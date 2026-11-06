import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0590_0_checked : (List.range' 302080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0590_1_checked : (List.range' 302208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0590_2_checked : (List.range' 302336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0590_3_checked : (List.range' 302464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0590_range (index : Nat) (lower : 302080 ≤ index) (upper : index < 302592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 302336 then
    if cut : index < 302208 then
      exact segment_sound _ 302080 128 Restriction0590_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 302208 128 Restriction0590_1_checked index (by omega) (by omega)
  else
    if cut : index < 302464 then
      exact segment_sound _ 302336 128 Restriction0590_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 302464 128 Restriction0590_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
