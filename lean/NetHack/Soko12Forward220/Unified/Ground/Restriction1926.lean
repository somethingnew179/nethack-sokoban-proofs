import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1926_0_checked : (List.range' 986112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1926_1_checked : (List.range' 986240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1926_2_checked : (List.range' 986368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1926_3_checked : (List.range' 986496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1926_range (index : Nat) (lower : 986112 ≤ index) (upper : index < 986624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 986368 then
    if cut : index < 986240 then
      exact segment_sound _ 986112 128 Restriction1926_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 986240 128 Restriction1926_1_checked index (by omega) (by omega)
  else
    if cut : index < 986496 then
      exact segment_sound _ 986368 128 Restriction1926_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 986496 128 Restriction1926_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
