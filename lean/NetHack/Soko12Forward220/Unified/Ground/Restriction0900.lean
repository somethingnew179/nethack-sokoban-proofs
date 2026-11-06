import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0900_0_checked : (List.range' 460800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0900_1_checked : (List.range' 460928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0900_2_checked : (List.range' 461056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0900_3_checked : (List.range' 461184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0900_range (index : Nat) (lower : 460800 ≤ index) (upper : index < 461312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 461056 then
    if cut : index < 460928 then
      exact segment_sound _ 460800 128 Restriction0900_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 460928 128 Restriction0900_1_checked index (by omega) (by omega)
  else
    if cut : index < 461184 then
      exact segment_sound _ 461056 128 Restriction0900_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 461184 128 Restriction0900_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
