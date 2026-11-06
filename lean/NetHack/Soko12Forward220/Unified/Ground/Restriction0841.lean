import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0841_0_checked : (List.range' 430592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0841_1_checked : (List.range' 430720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0841_2_checked : (List.range' 430848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0841_3_checked : (List.range' 430976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0841_range (index : Nat) (lower : 430592 ≤ index) (upper : index < 431104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 430848 then
    if cut : index < 430720 then
      exact segment_sound _ 430592 128 Restriction0841_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 430720 128 Restriction0841_1_checked index (by omega) (by omega)
  else
    if cut : index < 430976 then
      exact segment_sound _ 430848 128 Restriction0841_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 430976 128 Restriction0841_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
