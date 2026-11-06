import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0967_0_checked : (List.range' 495104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0967_1_checked : (List.range' 495232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0967_2_checked : (List.range' 495360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0967_3_checked : (List.range' 495488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0967_range (index : Nat) (lower : 495104 ≤ index) (upper : index < 495616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 495360 then
    if cut : index < 495232 then
      exact segment_sound _ 495104 128 Restriction0967_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 495232 128 Restriction0967_1_checked index (by omega) (by omega)
  else
    if cut : index < 495488 then
      exact segment_sound _ 495360 128 Restriction0967_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 495488 128 Restriction0967_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
