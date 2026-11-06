import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1582_0_checked : (List.range' 809984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1582_1_checked : (List.range' 810112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1582_2_checked : (List.range' 810240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1582_3_checked : (List.range' 810368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1582_range (index : Nat) (lower : 809984 ≤ index) (upper : index < 810496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 810240 then
    if cut : index < 810112 then
      exact segment_sound _ 809984 128 Restriction1582_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 810112 128 Restriction1582_1_checked index (by omega) (by omega)
  else
    if cut : index < 810368 then
      exact segment_sound _ 810240 128 Restriction1582_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 810368 128 Restriction1582_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
