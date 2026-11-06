import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1598_0_checked : (List.range' 818176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1598_1_checked : (List.range' 818304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1598_2_checked : (List.range' 818432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1598_3_checked : (List.range' 818560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1598_range (index : Nat) (lower : 818176 ≤ index) (upper : index < 818688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 818432 then
    if cut : index < 818304 then
      exact segment_sound _ 818176 128 Restriction1598_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 818304 128 Restriction1598_1_checked index (by omega) (by omega)
  else
    if cut : index < 818560 then
      exact segment_sound _ 818432 128 Restriction1598_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 818560 128 Restriction1598_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
