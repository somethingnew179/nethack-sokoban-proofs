import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0018_0_checked : (List.range' 9216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0018_1_checked : (List.range' 9344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0018_2_checked : (List.range' 9472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0018_3_checked : (List.range' 9600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0018_range (index : Nat) (lower : 9216 ≤ index) (upper : index < 9728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 9472 then
    if cut : index < 9344 then
      exact segment_sound _ 9216 128 Restriction0018_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 9344 128 Restriction0018_1_checked index (by omega) (by omega)
  else
    if cut : index < 9600 then
      exact segment_sound _ 9472 128 Restriction0018_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 9600 128 Restriction0018_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
