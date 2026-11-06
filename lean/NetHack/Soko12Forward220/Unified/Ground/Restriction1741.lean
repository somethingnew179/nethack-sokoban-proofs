import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1741_0_checked : (List.range' 891392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1741_1_checked : (List.range' 891520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1741_2_checked : (List.range' 891648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1741_3_checked : (List.range' 891776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1741_range (index : Nat) (lower : 891392 ≤ index) (upper : index < 891904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 891648 then
    if cut : index < 891520 then
      exact segment_sound _ 891392 128 Restriction1741_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 891520 128 Restriction1741_1_checked index (by omega) (by omega)
  else
    if cut : index < 891776 then
      exact segment_sound _ 891648 128 Restriction1741_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 891776 128 Restriction1741_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
