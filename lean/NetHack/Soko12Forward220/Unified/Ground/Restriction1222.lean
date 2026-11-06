import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1222_0_checked : (List.range' 625664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1222_1_checked : (List.range' 625792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1222_2_checked : (List.range' 625920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1222_3_checked : (List.range' 626048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1222_range (index : Nat) (lower : 625664 ≤ index) (upper : index < 626176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 625920 then
    if cut : index < 625792 then
      exact segment_sound _ 625664 128 Restriction1222_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 625792 128 Restriction1222_1_checked index (by omega) (by omega)
  else
    if cut : index < 626048 then
      exact segment_sound _ 625920 128 Restriction1222_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 626048 128 Restriction1222_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
