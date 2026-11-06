import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0806_0_checked : (List.range' 412672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0806_1_checked : (List.range' 412800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0806_2_checked : (List.range' 412928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0806_3_checked : (List.range' 413056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0806_range (index : Nat) (lower : 412672 ≤ index) (upper : index < 413184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 412928 then
    if cut : index < 412800 then
      exact segment_sound _ 412672 128 Restriction0806_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 412800 128 Restriction0806_1_checked index (by omega) (by omega)
  else
    if cut : index < 413056 then
      exact segment_sound _ 412928 128 Restriction0806_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 413056 128 Restriction0806_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
