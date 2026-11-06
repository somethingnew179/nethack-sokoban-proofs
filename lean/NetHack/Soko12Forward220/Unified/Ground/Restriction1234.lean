import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1234_0_checked : (List.range' 631808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1234_1_checked : (List.range' 631936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1234_2_checked : (List.range' 632064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1234_3_checked : (List.range' 632192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1234_range (index : Nat) (lower : 631808 ≤ index) (upper : index < 632320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 632064 then
    if cut : index < 631936 then
      exact segment_sound _ 631808 128 Restriction1234_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 631936 128 Restriction1234_1_checked index (by omega) (by omega)
  else
    if cut : index < 632192 then
      exact segment_sound _ 632064 128 Restriction1234_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 632192 128 Restriction1234_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
