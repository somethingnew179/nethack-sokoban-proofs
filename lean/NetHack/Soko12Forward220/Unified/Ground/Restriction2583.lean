import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2583_0_checked : (List.range' 1322496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2583_1_checked : (List.range' 1322624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2583_2_checked : (List.range' 1322752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2583_3_checked : (List.range' 1322880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2583_range (index : Nat) (lower : 1322496 ≤ index) (upper : index < 1323008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1322752 then
    if cut : index < 1322624 then
      exact segment_sound _ 1322496 128 Restriction2583_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1322624 128 Restriction2583_1_checked index (by omega) (by omega)
  else
    if cut : index < 1322880 then
      exact segment_sound _ 1322752 128 Restriction2583_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1322880 128 Restriction2583_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
