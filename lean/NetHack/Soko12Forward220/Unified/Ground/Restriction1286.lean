import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1286_0_checked : (List.range' 658432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1286_1_checked : (List.range' 658560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1286_2_checked : (List.range' 658688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1286_3_checked : (List.range' 658816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1286_range (index : Nat) (lower : 658432 ≤ index) (upper : index < 658944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 658688 then
    if cut : index < 658560 then
      exact segment_sound _ 658432 128 Restriction1286_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 658560 128 Restriction1286_1_checked index (by omega) (by omega)
  else
    if cut : index < 658816 then
      exact segment_sound _ 658688 128 Restriction1286_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 658816 128 Restriction1286_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
