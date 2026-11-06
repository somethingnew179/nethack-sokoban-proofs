import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0204_0_checked : (List.range' 104448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0204_1_checked : (List.range' 104576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0204_2_checked : (List.range' 104704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0204_3_checked : (List.range' 104832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0204_range (index : Nat) (lower : 104448 ≤ index) (upper : index < 104960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 104704 then
    if cut : index < 104576 then
      exact segment_sound _ 104448 128 Restriction0204_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 104576 128 Restriction0204_1_checked index (by omega) (by omega)
  else
    if cut : index < 104832 then
      exact segment_sound _ 104704 128 Restriction0204_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 104832 128 Restriction0204_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
