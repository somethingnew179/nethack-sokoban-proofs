import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0782_0_checked : (List.range' 400384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0782_1_checked : (List.range' 400512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0782_2_checked : (List.range' 400640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0782_3_checked : (List.range' 400768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0782_range (index : Nat) (lower : 400384 ≤ index) (upper : index < 400896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 400640 then
    if cut : index < 400512 then
      exact segment_sound _ 400384 128 Restriction0782_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 400512 128 Restriction0782_1_checked index (by omega) (by omega)
  else
    if cut : index < 400768 then
      exact segment_sound _ 400640 128 Restriction0782_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 400768 128 Restriction0782_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
