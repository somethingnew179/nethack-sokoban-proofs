import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0879_0_checked : (List.range' 450048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0879_1_checked : (List.range' 450176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0879_2_checked : (List.range' 450304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0879_3_checked : (List.range' 450432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0879_range (index : Nat) (lower : 450048 ≤ index) (upper : index < 450560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 450304 then
    if cut : index < 450176 then
      exact segment_sound _ 450048 128 Restriction0879_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 450176 128 Restriction0879_1_checked index (by omega) (by omega)
  else
    if cut : index < 450432 then
      exact segment_sound _ 450304 128 Restriction0879_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 450432 128 Restriction0879_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
