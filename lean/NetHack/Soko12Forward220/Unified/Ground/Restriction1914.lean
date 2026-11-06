import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1914_0_checked : (List.range' 979968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1914_1_checked : (List.range' 980096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1914_2_checked : (List.range' 980224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1914_3_checked : (List.range' 980352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1914_range (index : Nat) (lower : 979968 ≤ index) (upper : index < 980480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 980224 then
    if cut : index < 980096 then
      exact segment_sound _ 979968 128 Restriction1914_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 980096 128 Restriction1914_1_checked index (by omega) (by omega)
  else
    if cut : index < 980352 then
      exact segment_sound _ 980224 128 Restriction1914_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 980352 128 Restriction1914_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
