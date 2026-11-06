import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1580_0_checked : (List.range' 808960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1580_1_checked : (List.range' 809088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1580_2_checked : (List.range' 809216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1580_3_checked : (List.range' 809344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1580_range (index : Nat) (lower : 808960 ≤ index) (upper : index < 809472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 809216 then
    if cut : index < 809088 then
      exact segment_sound _ 808960 128 Restriction1580_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 809088 128 Restriction1580_1_checked index (by omega) (by omega)
  else
    if cut : index < 809344 then
      exact segment_sound _ 809216 128 Restriction1580_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 809344 128 Restriction1580_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
