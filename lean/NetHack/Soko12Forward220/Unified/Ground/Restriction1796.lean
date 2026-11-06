import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1796_0_checked : (List.range' 919552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1796_1_checked : (List.range' 919680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1796_2_checked : (List.range' 919808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1796_3_checked : (List.range' 919936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1796_range (index : Nat) (lower : 919552 ≤ index) (upper : index < 920064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 919808 then
    if cut : index < 919680 then
      exact segment_sound _ 919552 128 Restriction1796_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 919680 128 Restriction1796_1_checked index (by omega) (by omega)
  else
    if cut : index < 919936 then
      exact segment_sound _ 919808 128 Restriction1796_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 919936 128 Restriction1796_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
