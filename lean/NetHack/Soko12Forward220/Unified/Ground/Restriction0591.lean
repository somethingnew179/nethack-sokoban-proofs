import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0591_0_checked : (List.range' 302592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0591_1_checked : (List.range' 302720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0591_2_checked : (List.range' 302848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0591_3_checked : (List.range' 302976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0591_range (index : Nat) (lower : 302592 ≤ index) (upper : index < 303104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 302848 then
    if cut : index < 302720 then
      exact segment_sound _ 302592 128 Restriction0591_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 302720 128 Restriction0591_1_checked index (by omega) (by omega)
  else
    if cut : index < 302976 then
      exact segment_sound _ 302848 128 Restriction0591_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 302976 128 Restriction0591_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
