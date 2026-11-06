import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2463_0_checked : (List.range' 1261056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2463_1_checked : (List.range' 1261184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2463_2_checked : (List.range' 1261312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2463_3_checked : (List.range' 1261440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2463_range (index : Nat) (lower : 1261056 ≤ index) (upper : index < 1261568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1261312 then
    if cut : index < 1261184 then
      exact segment_sound _ 1261056 128 Restriction2463_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1261184 128 Restriction2463_1_checked index (by omega) (by omega)
  else
    if cut : index < 1261440 then
      exact segment_sound _ 1261312 128 Restriction2463_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1261440 128 Restriction2463_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
