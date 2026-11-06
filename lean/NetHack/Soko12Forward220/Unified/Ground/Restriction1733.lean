import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1733_0_checked : (List.range' 887296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1733_1_checked : (List.range' 887424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1733_2_checked : (List.range' 887552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1733_3_checked : (List.range' 887680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1733_range (index : Nat) (lower : 887296 ≤ index) (upper : index < 887808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 887552 then
    if cut : index < 887424 then
      exact segment_sound _ 887296 128 Restriction1733_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 887424 128 Restriction1733_1_checked index (by omega) (by omega)
  else
    if cut : index < 887680 then
      exact segment_sound _ 887552 128 Restriction1733_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 887680 128 Restriction1733_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
