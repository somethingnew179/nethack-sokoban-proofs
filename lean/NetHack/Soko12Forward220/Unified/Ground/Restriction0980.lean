import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0980_0_checked : (List.range' 501760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0980_1_checked : (List.range' 501888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0980_2_checked : (List.range' 502016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0980_3_checked : (List.range' 502144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0980_range (index : Nat) (lower : 501760 ≤ index) (upper : index < 502272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 502016 then
    if cut : index < 501888 then
      exact segment_sound _ 501760 128 Restriction0980_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 501888 128 Restriction0980_1_checked index (by omega) (by omega)
  else
    if cut : index < 502144 then
      exact segment_sound _ 502016 128 Restriction0980_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 502144 128 Restriction0980_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
