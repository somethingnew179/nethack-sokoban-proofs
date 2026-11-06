import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1233_0_checked : (List.range' 631296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1233_1_checked : (List.range' 631424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1233_2_checked : (List.range' 631552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1233_3_checked : (List.range' 631680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1233_range (index : Nat) (lower : 631296 ≤ index) (upper : index < 631808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 631552 then
    if cut : index < 631424 then
      exact segment_sound _ 631296 128 Restriction1233_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 631424 128 Restriction1233_1_checked index (by omega) (by omega)
  else
    if cut : index < 631680 then
      exact segment_sound _ 631552 128 Restriction1233_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 631680 128 Restriction1233_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
