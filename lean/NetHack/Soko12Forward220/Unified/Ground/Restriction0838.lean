import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0838_0_checked : (List.range' 429056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0838_1_checked : (List.range' 429184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0838_2_checked : (List.range' 429312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0838_3_checked : (List.range' 429440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0838_range (index : Nat) (lower : 429056 ≤ index) (upper : index < 429568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 429312 then
    if cut : index < 429184 then
      exact segment_sound _ 429056 128 Restriction0838_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 429184 128 Restriction0838_1_checked index (by omega) (by omega)
  else
    if cut : index < 429440 then
      exact segment_sound _ 429312 128 Restriction0838_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 429440 128 Restriction0838_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
