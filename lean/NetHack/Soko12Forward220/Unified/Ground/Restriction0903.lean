import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0903_0_checked : (List.range' 462336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0903_1_checked : (List.range' 462464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0903_2_checked : (List.range' 462592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0903_3_checked : (List.range' 462720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0903_range (index : Nat) (lower : 462336 ≤ index) (upper : index < 462848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 462592 then
    if cut : index < 462464 then
      exact segment_sound _ 462336 128 Restriction0903_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 462464 128 Restriction0903_1_checked index (by omega) (by omega)
  else
    if cut : index < 462720 then
      exact segment_sound _ 462592 128 Restriction0903_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 462720 128 Restriction0903_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
