import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1820_0_checked : (List.range' 931840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1820_1_checked : (List.range' 931968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1820_2_checked : (List.range' 932096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1820_3_checked : (List.range' 932224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1820_range (index : Nat) (lower : 931840 ≤ index) (upper : index < 932352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 932096 then
    if cut : index < 931968 then
      exact segment_sound _ 931840 128 Restriction1820_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 931968 128 Restriction1820_1_checked index (by omega) (by omega)
  else
    if cut : index < 932224 then
      exact segment_sound _ 932096 128 Restriction1820_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 932224 128 Restriction1820_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
