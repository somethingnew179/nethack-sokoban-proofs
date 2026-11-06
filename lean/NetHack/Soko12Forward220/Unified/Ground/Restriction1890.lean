import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1890_0_checked : (List.range' 967680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1890_1_checked : (List.range' 967808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1890_2_checked : (List.range' 967936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1890_3_checked : (List.range' 968064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1890_range (index : Nat) (lower : 967680 ≤ index) (upper : index < 968192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 967936 then
    if cut : index < 967808 then
      exact segment_sound _ 967680 128 Restriction1890_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 967808 128 Restriction1890_1_checked index (by omega) (by omega)
  else
    if cut : index < 968064 then
      exact segment_sound _ 967936 128 Restriction1890_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 968064 128 Restriction1890_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
