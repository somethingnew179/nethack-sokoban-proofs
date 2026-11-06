import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1819_0_checked : (List.range' 931328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1819_1_checked : (List.range' 931456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1819_2_checked : (List.range' 931584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1819_3_checked : (List.range' 931712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1819_range (index : Nat) (lower : 931328 ≤ index) (upper : index < 931840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 931584 then
    if cut : index < 931456 then
      exact segment_sound _ 931328 128 Restriction1819_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 931456 128 Restriction1819_1_checked index (by omega) (by omega)
  else
    if cut : index < 931712 then
      exact segment_sound _ 931584 128 Restriction1819_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 931712 128 Restriction1819_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
