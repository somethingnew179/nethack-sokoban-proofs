import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0981_0_checked : (List.range' 502272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0981_1_checked : (List.range' 502400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0981_2_checked : (List.range' 502528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0981_3_checked : (List.range' 502656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0981_range (index : Nat) (lower : 502272 ≤ index) (upper : index < 502784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 502528 then
    if cut : index < 502400 then
      exact segment_sound _ 502272 128 Restriction0981_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 502400 128 Restriction0981_1_checked index (by omega) (by omega)
  else
    if cut : index < 502656 then
      exact segment_sound _ 502528 128 Restriction0981_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 502656 128 Restriction0981_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
