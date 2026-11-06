import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1845_0_checked : (List.range' 944640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1845_1_checked : (List.range' 944768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1845_2_checked : (List.range' 944896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1845_3_checked : (List.range' 945024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1845_range (index : Nat) (lower : 944640 ≤ index) (upper : index < 945152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 944896 then
    if cut : index < 944768 then
      exact segment_sound _ 944640 128 Restriction1845_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 944768 128 Restriction1845_1_checked index (by omega) (by omega)
  else
    if cut : index < 945024 then
      exact segment_sound _ 944896 128 Restriction1845_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 945024 128 Restriction1845_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
