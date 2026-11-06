import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2045_0_checked : (List.range' 1047040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2045_1_checked : (List.range' 1047168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2045_2_checked : (List.range' 1047296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2045_3_checked : (List.range' 1047424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2045_range (index : Nat) (lower : 1047040 ≤ index) (upper : index < 1047552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1047296 then
    if cut : index < 1047168 then
      exact segment_sound _ 1047040 128 Restriction2045_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1047168 128 Restriction2045_1_checked index (by omega) (by omega)
  else
    if cut : index < 1047424 then
      exact segment_sound _ 1047296 128 Restriction2045_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1047424 128 Restriction2045_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
