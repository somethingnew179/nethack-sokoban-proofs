import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1701_0_checked : (List.range' 870912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1701_1_checked : (List.range' 871040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1701_2_checked : (List.range' 871168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1701_3_checked : (List.range' 871296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1701_range (index : Nat) (lower : 870912 ≤ index) (upper : index < 871424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 871168 then
    if cut : index < 871040 then
      exact segment_sound _ 870912 128 Restriction1701_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 871040 128 Restriction1701_1_checked index (by omega) (by omega)
  else
    if cut : index < 871296 then
      exact segment_sound _ 871168 128 Restriction1701_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 871296 128 Restriction1701_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
