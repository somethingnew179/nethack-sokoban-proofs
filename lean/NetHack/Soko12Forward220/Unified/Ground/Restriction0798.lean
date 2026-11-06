import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0798_0_checked : (List.range' 408576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0798_1_checked : (List.range' 408704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0798_2_checked : (List.range' 408832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0798_3_checked : (List.range' 408960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0798_range (index : Nat) (lower : 408576 ≤ index) (upper : index < 409088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 408832 then
    if cut : index < 408704 then
      exact segment_sound _ 408576 128 Restriction0798_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 408704 128 Restriction0798_1_checked index (by omega) (by omega)
  else
    if cut : index < 408960 then
      exact segment_sound _ 408832 128 Restriction0798_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 408960 128 Restriction0798_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
