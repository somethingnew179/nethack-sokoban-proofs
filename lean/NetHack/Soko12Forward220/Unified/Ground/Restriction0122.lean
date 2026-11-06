import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0122_0_checked : (List.range' 62464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0122_1_checked : (List.range' 62592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0122_2_checked : (List.range' 62720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0122_3_checked : (List.range' 62848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0122_range (index : Nat) (lower : 62464 ≤ index) (upper : index < 62976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 62720 then
    if cut : index < 62592 then
      exact segment_sound _ 62464 128 Restriction0122_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 62592 128 Restriction0122_1_checked index (by omega) (by omega)
  else
    if cut : index < 62848 then
      exact segment_sound _ 62720 128 Restriction0122_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 62848 128 Restriction0122_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
