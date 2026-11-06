import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1736_0_checked : (List.range' 888832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1736_1_checked : (List.range' 888960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1736_2_checked : (List.range' 889088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1736_3_checked : (List.range' 889216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1736_range (index : Nat) (lower : 888832 ≤ index) (upper : index < 889344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 889088 then
    if cut : index < 888960 then
      exact segment_sound _ 888832 128 Restriction1736_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 888960 128 Restriction1736_1_checked index (by omega) (by omega)
  else
    if cut : index < 889216 then
      exact segment_sound _ 889088 128 Restriction1736_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 889216 128 Restriction1736_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
