import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0759_0_checked : (List.range' 388608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0759_1_checked : (List.range' 388736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0759_2_checked : (List.range' 388864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0759_3_checked : (List.range' 388992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0759_range (index : Nat) (lower : 388608 ≤ index) (upper : index < 389120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 388864 then
    if cut : index < 388736 then
      exact segment_sound _ 388608 128 Restriction0759_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 388736 128 Restriction0759_1_checked index (by omega) (by omega)
  else
    if cut : index < 388992 then
      exact segment_sound _ 388864 128 Restriction0759_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 388992 128 Restriction0759_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
