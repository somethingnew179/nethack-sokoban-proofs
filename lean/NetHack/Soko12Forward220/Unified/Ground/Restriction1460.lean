import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1460_0_checked : (List.range' 747520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1460_1_checked : (List.range' 747648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1460_2_checked : (List.range' 747776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1460_3_checked : (List.range' 747904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1460_range (index : Nat) (lower : 747520 ≤ index) (upper : index < 748032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 747776 then
    if cut : index < 747648 then
      exact segment_sound _ 747520 128 Restriction1460_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 747648 128 Restriction1460_1_checked index (by omega) (by omega)
  else
    if cut : index < 747904 then
      exact segment_sound _ 747776 128 Restriction1460_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 747904 128 Restriction1460_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
