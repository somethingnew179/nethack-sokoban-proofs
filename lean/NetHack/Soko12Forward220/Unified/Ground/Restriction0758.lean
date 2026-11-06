import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0758_0_checked : (List.range' 388096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0758_1_checked : (List.range' 388224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0758_2_checked : (List.range' 388352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0758_3_checked : (List.range' 388480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0758_range (index : Nat) (lower : 388096 ≤ index) (upper : index < 388608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 388352 then
    if cut : index < 388224 then
      exact segment_sound _ 388096 128 Restriction0758_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 388224 128 Restriction0758_1_checked index (by omega) (by omega)
  else
    if cut : index < 388480 then
      exact segment_sound _ 388352 128 Restriction0758_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 388480 128 Restriction0758_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
