import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1068_0_checked : (List.range' 546816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1068_1_checked : (List.range' 546944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1068_2_checked : (List.range' 547072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1068_3_checked : (List.range' 547200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1068_range (index : Nat) (lower : 546816 ≤ index) (upper : index < 547328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 547072 then
    if cut : index < 546944 then
      exact segment_sound _ 546816 128 Restriction1068_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 546944 128 Restriction1068_1_checked index (by omega) (by omega)
  else
    if cut : index < 547200 then
      exact segment_sound _ 547072 128 Restriction1068_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 547200 128 Restriction1068_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
