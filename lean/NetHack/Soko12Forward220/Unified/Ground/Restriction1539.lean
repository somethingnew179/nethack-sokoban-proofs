import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1539_0_checked : (List.range' 787968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1539_1_checked : (List.range' 788096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1539_2_checked : (List.range' 788224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1539_3_checked : (List.range' 788352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1539_range (index : Nat) (lower : 787968 ≤ index) (upper : index < 788480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 788224 then
    if cut : index < 788096 then
      exact segment_sound _ 787968 128 Restriction1539_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 788096 128 Restriction1539_1_checked index (by omega) (by omega)
  else
    if cut : index < 788352 then
      exact segment_sound _ 788224 128 Restriction1539_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 788352 128 Restriction1539_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
