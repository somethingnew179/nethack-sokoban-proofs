import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1545_0_checked : (List.range' 791040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1545_1_checked : (List.range' 791168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1545_2_checked : (List.range' 791296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1545_3_checked : (List.range' 791424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1545_range (index : Nat) (lower : 791040 ≤ index) (upper : index < 791552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 791296 then
    if cut : index < 791168 then
      exact segment_sound _ 791040 128 Restriction1545_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 791168 128 Restriction1545_1_checked index (by omega) (by omega)
  else
    if cut : index < 791424 then
      exact segment_sound _ 791296 128 Restriction1545_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 791424 128 Restriction1545_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
