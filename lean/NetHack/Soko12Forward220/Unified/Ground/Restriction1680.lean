import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1680_0_checked : (List.range' 860160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1680_1_checked : (List.range' 860288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1680_2_checked : (List.range' 860416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1680_3_checked : (List.range' 860544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1680_range (index : Nat) (lower : 860160 ≤ index) (upper : index < 860672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 860416 then
    if cut : index < 860288 then
      exact segment_sound _ 860160 128 Restriction1680_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 860288 128 Restriction1680_1_checked index (by omega) (by omega)
  else
    if cut : index < 860544 then
      exact segment_sound _ 860416 128 Restriction1680_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 860544 128 Restriction1680_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
