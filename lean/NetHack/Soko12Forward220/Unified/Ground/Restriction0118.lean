import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0118_0_checked : (List.range' 60416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0118_1_checked : (List.range' 60544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0118_2_checked : (List.range' 60672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0118_3_checked : (List.range' 60800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0118_range (index : Nat) (lower : 60416 ≤ index) (upper : index < 60928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 60672 then
    if cut : index < 60544 then
      exact segment_sound _ 60416 128 Restriction0118_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 60544 128 Restriction0118_1_checked index (by omega) (by omega)
  else
    if cut : index < 60800 then
      exact segment_sound _ 60672 128 Restriction0118_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 60800 128 Restriction0118_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
