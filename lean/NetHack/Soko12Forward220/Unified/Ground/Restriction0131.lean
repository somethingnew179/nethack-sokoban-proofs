import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0131_0_checked : (List.range' 67072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0131_1_checked : (List.range' 67200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0131_2_checked : (List.range' 67328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0131_3_checked : (List.range' 67456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0131_range (index : Nat) (lower : 67072 ≤ index) (upper : index < 67584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 67328 then
    if cut : index < 67200 then
      exact segment_sound _ 67072 128 Restriction0131_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 67200 128 Restriction0131_1_checked index (by omega) (by omega)
  else
    if cut : index < 67456 then
      exact segment_sound _ 67328 128 Restriction0131_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 67456 128 Restriction0131_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
