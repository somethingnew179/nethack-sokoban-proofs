import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0520_0_checked : (List.range' 266240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0520_1_checked : (List.range' 266368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0520_2_checked : (List.range' 266496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0520_3_checked : (List.range' 266624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0520_range (index : Nat) (lower : 266240 ≤ index) (upper : index < 266752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 266496 then
    if cut : index < 266368 then
      exact segment_sound _ 266240 128 Restriction0520_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 266368 128 Restriction0520_1_checked index (by omega) (by omega)
  else
    if cut : index < 266624 then
      exact segment_sound _ 266496 128 Restriction0520_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 266624 128 Restriction0520_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
