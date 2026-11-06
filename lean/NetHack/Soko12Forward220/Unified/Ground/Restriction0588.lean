import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0588_0_checked : (List.range' 301056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0588_1_checked : (List.range' 301184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0588_2_checked : (List.range' 301312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0588_3_checked : (List.range' 301440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0588_range (index : Nat) (lower : 301056 ≤ index) (upper : index < 301568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 301312 then
    if cut : index < 301184 then
      exact segment_sound _ 301056 128 Restriction0588_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 301184 128 Restriction0588_1_checked index (by omega) (by omega)
  else
    if cut : index < 301440 then
      exact segment_sound _ 301312 128 Restriction0588_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 301440 128 Restriction0588_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
