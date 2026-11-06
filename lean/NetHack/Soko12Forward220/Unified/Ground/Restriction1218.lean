import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1218_0_checked : (List.range' 623616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1218_1_checked : (List.range' 623744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1218_2_checked : (List.range' 623872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1218_3_checked : (List.range' 624000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1218_range (index : Nat) (lower : 623616 ≤ index) (upper : index < 624128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 623872 then
    if cut : index < 623744 then
      exact segment_sound _ 623616 128 Restriction1218_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 623744 128 Restriction1218_1_checked index (by omega) (by omega)
  else
    if cut : index < 624000 then
      exact segment_sound _ 623872 128 Restriction1218_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 624000 128 Restriction1218_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
