import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1722_0_checked : (List.range' 881664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1722_1_checked : (List.range' 881792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1722_2_checked : (List.range' 881920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1722_3_checked : (List.range' 882048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1722_range (index : Nat) (lower : 881664 ≤ index) (upper : index < 882176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 881920 then
    if cut : index < 881792 then
      exact segment_sound _ 881664 128 Restriction1722_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 881792 128 Restriction1722_1_checked index (by omega) (by omega)
  else
    if cut : index < 882048 then
      exact segment_sound _ 881920 128 Restriction1722_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 882048 128 Restriction1722_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
