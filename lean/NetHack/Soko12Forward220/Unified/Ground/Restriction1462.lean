import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1462_0_checked : (List.range' 748544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1462_1_checked : (List.range' 748672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1462_2_checked : (List.range' 748800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1462_3_checked : (List.range' 748928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1462_range (index : Nat) (lower : 748544 ≤ index) (upper : index < 749056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 748800 then
    if cut : index < 748672 then
      exact segment_sound _ 748544 128 Restriction1462_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 748672 128 Restriction1462_1_checked index (by omega) (by omega)
  else
    if cut : index < 748928 then
      exact segment_sound _ 748800 128 Restriction1462_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 748928 128 Restriction1462_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
