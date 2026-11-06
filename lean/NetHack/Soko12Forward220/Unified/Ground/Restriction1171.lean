import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1171_0_checked : (List.range' 599552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1171_1_checked : (List.range' 599680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1171_2_checked : (List.range' 599808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1171_3_checked : (List.range' 599936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1171_range (index : Nat) (lower : 599552 ≤ index) (upper : index < 600064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 599808 then
    if cut : index < 599680 then
      exact segment_sound _ 599552 128 Restriction1171_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 599680 128 Restriction1171_1_checked index (by omega) (by omega)
  else
    if cut : index < 599936 then
      exact segment_sound _ 599808 128 Restriction1171_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 599936 128 Restriction1171_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
