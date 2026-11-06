import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2621_0_checked : (List.range' 1341952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2621_1_checked : (List.range' 1342080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2621_2_checked : (List.range' 1342208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2621_3_checked : (List.range' 1342336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2621_range (index : Nat) (lower : 1341952 ≤ index) (upper : index < 1342464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1342208 then
    if cut : index < 1342080 then
      exact segment_sound _ 1341952 128 Restriction2621_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1342080 128 Restriction2621_1_checked index (by omega) (by omega)
  else
    if cut : index < 1342336 then
      exact segment_sound _ 1342208 128 Restriction2621_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1342336 128 Restriction2621_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
