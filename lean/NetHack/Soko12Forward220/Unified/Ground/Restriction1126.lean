import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1126_0_checked : (List.range' 576512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1126_1_checked : (List.range' 576640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1126_2_checked : (List.range' 576768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1126_3_checked : (List.range' 576896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1126_range (index : Nat) (lower : 576512 ≤ index) (upper : index < 577024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 576768 then
    if cut : index < 576640 then
      exact segment_sound _ 576512 128 Restriction1126_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 576640 128 Restriction1126_1_checked index (by omega) (by omega)
  else
    if cut : index < 576896 then
      exact segment_sound _ 576768 128 Restriction1126_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 576896 128 Restriction1126_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
