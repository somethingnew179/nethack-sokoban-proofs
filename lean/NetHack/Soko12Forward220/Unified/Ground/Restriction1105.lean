import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1105_0_checked : (List.range' 565760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1105_1_checked : (List.range' 565888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1105_2_checked : (List.range' 566016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1105_3_checked : (List.range' 566144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1105_range (index : Nat) (lower : 565760 ≤ index) (upper : index < 566272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 566016 then
    if cut : index < 565888 then
      exact segment_sound _ 565760 128 Restriction1105_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 565888 128 Restriction1105_1_checked index (by omega) (by omega)
  else
    if cut : index < 566144 then
      exact segment_sound _ 566016 128 Restriction1105_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 566144 128 Restriction1105_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
