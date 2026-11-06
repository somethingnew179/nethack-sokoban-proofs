import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2337_0_checked : (List.range' 1196544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2337_1_checked : (List.range' 1196672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2337_2_checked : (List.range' 1196800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2337_3_checked : (List.range' 1196928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2337_range (index : Nat) (lower : 1196544 ≤ index) (upper : index < 1197056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1196800 then
    if cut : index < 1196672 then
      exact segment_sound _ 1196544 128 Restriction2337_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1196672 128 Restriction2337_1_checked index (by omega) (by omega)
  else
    if cut : index < 1196928 then
      exact segment_sound _ 1196800 128 Restriction2337_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1196928 128 Restriction2337_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
