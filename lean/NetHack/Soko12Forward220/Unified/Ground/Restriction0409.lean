import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0409_0_checked : (List.range' 209408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0409_1_checked : (List.range' 209536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0409_2_checked : (List.range' 209664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0409_3_checked : (List.range' 209792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0409_range (index : Nat) (lower : 209408 ≤ index) (upper : index < 209920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 209664 then
    if cut : index < 209536 then
      exact segment_sound _ 209408 128 Restriction0409_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 209536 128 Restriction0409_1_checked index (by omega) (by omega)
  else
    if cut : index < 209792 then
      exact segment_sound _ 209664 128 Restriction0409_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 209792 128 Restriction0409_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
