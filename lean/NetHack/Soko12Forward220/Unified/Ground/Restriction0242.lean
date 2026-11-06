import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0242_0_checked : (List.range' 123904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0242_1_checked : (List.range' 124032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0242_2_checked : (List.range' 124160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0242_3_checked : (List.range' 124288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0242_range (index : Nat) (lower : 123904 ≤ index) (upper : index < 124416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 124160 then
    if cut : index < 124032 then
      exact segment_sound _ 123904 128 Restriction0242_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 124032 128 Restriction0242_1_checked index (by omega) (by omega)
  else
    if cut : index < 124288 then
      exact segment_sound _ 124160 128 Restriction0242_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 124288 128 Restriction0242_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
