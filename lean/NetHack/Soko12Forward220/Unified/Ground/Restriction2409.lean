import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2409_0_checked : (List.range' 1233408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2409_1_checked : (List.range' 1233536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2409_2_checked : (List.range' 1233664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2409_3_checked : (List.range' 1233792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2409_range (index : Nat) (lower : 1233408 ≤ index) (upper : index < 1233920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1233664 then
    if cut : index < 1233536 then
      exact segment_sound _ 1233408 128 Restriction2409_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1233536 128 Restriction2409_1_checked index (by omega) (by omega)
  else
    if cut : index < 1233792 then
      exact segment_sound _ 1233664 128 Restriction2409_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1233792 128 Restriction2409_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
