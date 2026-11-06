import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0985_0_checked : (List.range' 504320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0985_1_checked : (List.range' 504448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0985_2_checked : (List.range' 504576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0985_3_checked : (List.range' 504704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0985_range (index : Nat) (lower : 504320 ≤ index) (upper : index < 504832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 504576 then
    if cut : index < 504448 then
      exact segment_sound _ 504320 128 Restriction0985_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 504448 128 Restriction0985_1_checked index (by omega) (by omega)
  else
    if cut : index < 504704 then
      exact segment_sound _ 504576 128 Restriction0985_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 504704 128 Restriction0985_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
