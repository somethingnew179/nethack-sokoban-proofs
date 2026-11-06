import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1468_0_checked : (List.range' 751616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1468_1_checked : (List.range' 751744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1468_2_checked : (List.range' 751872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1468_3_checked : (List.range' 752000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1468_range (index : Nat) (lower : 751616 ≤ index) (upper : index < 752128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 751872 then
    if cut : index < 751744 then
      exact segment_sound _ 751616 128 Restriction1468_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 751744 128 Restriction1468_1_checked index (by omega) (by omega)
  else
    if cut : index < 752000 then
      exact segment_sound _ 751872 128 Restriction1468_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 752000 128 Restriction1468_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
