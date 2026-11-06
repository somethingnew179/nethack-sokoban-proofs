import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1832_0_checked : (List.range' 937984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1832_1_checked : (List.range' 938112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1832_2_checked : (List.range' 938240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1832_3_checked : (List.range' 938368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1832_range (index : Nat) (lower : 937984 ≤ index) (upper : index < 938496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 938240 then
    if cut : index < 938112 then
      exact segment_sound _ 937984 128 Restriction1832_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 938112 128 Restriction1832_1_checked index (by omega) (by omega)
  else
    if cut : index < 938368 then
      exact segment_sound _ 938240 128 Restriction1832_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 938368 128 Restriction1832_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
