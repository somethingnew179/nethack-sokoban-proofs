import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1375_0_checked : (List.range' 704000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1375_1_checked : (List.range' 704128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1375_2_checked : (List.range' 704256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1375_3_checked : (List.range' 704384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1375_range (index : Nat) (lower : 704000 ≤ index) (upper : index < 704512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 704256 then
    if cut : index < 704128 then
      exact segment_sound _ 704000 128 Restriction1375_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 704128 128 Restriction1375_1_checked index (by omega) (by omega)
  else
    if cut : index < 704384 then
      exact segment_sound _ 704256 128 Restriction1375_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 704384 128 Restriction1375_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
