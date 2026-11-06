import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0666_0_checked : (List.range' 340992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0666_1_checked : (List.range' 341120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0666_2_checked : (List.range' 341248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0666_3_checked : (List.range' 341376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0666_range (index : Nat) (lower : 340992 ≤ index) (upper : index < 341504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 341248 then
    if cut : index < 341120 then
      exact segment_sound _ 340992 128 Restriction0666_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 341120 128 Restriction0666_1_checked index (by omega) (by omega)
  else
    if cut : index < 341376 then
      exact segment_sound _ 341248 128 Restriction0666_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 341376 128 Restriction0666_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
