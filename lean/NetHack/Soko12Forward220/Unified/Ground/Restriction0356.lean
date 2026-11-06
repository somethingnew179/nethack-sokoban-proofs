import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0356_0_checked : (List.range' 182272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0356_1_checked : (List.range' 182400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0356_2_checked : (List.range' 182528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0356_3_checked : (List.range' 182656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0356_range (index : Nat) (lower : 182272 ≤ index) (upper : index < 182784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 182528 then
    if cut : index < 182400 then
      exact segment_sound _ 182272 128 Restriction0356_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 182400 128 Restriction0356_1_checked index (by omega) (by omega)
  else
    if cut : index < 182656 then
      exact segment_sound _ 182528 128 Restriction0356_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 182656 128 Restriction0356_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
