import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1293_0_checked : (List.range' 662016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1293_1_checked : (List.range' 662144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1293_2_checked : (List.range' 662272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1293_3_checked : (List.range' 662400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1293_range (index : Nat) (lower : 662016 ≤ index) (upper : index < 662528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 662272 then
    if cut : index < 662144 then
      exact segment_sound _ 662016 128 Restriction1293_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 662144 128 Restriction1293_1_checked index (by omega) (by omega)
  else
    if cut : index < 662400 then
      exact segment_sound _ 662272 128 Restriction1293_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 662400 128 Restriction1293_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
