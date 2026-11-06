import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1034_0_checked : (List.range' 529408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1034_1_checked : (List.range' 529536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1034_2_checked : (List.range' 529664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1034_3_checked : (List.range' 529792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1034_range (index : Nat) (lower : 529408 ≤ index) (upper : index < 529920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 529664 then
    if cut : index < 529536 then
      exact segment_sound _ 529408 128 Restriction1034_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 529536 128 Restriction1034_1_checked index (by omega) (by omega)
  else
    if cut : index < 529792 then
      exact segment_sound _ 529664 128 Restriction1034_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 529792 128 Restriction1034_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
