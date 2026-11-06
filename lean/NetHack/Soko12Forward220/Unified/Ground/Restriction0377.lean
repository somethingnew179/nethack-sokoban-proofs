import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0377_0_checked : (List.range' 193024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0377_1_checked : (List.range' 193152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0377_2_checked : (List.range' 193280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0377_3_checked : (List.range' 193408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0377_range (index : Nat) (lower : 193024 ≤ index) (upper : index < 193536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 193280 then
    if cut : index < 193152 then
      exact segment_sound _ 193024 128 Restriction0377_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 193152 128 Restriction0377_1_checked index (by omega) (by omega)
  else
    if cut : index < 193408 then
      exact segment_sound _ 193280 128 Restriction0377_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 193408 128 Restriction0377_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
