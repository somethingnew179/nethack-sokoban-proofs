import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2574_0_checked : (List.range' 1317888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2574_1_checked : (List.range' 1318016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2574_2_checked : (List.range' 1318144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2574_3_checked : (List.range' 1318272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2574_range (index : Nat) (lower : 1317888 ≤ index) (upper : index < 1318400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1318144 then
    if cut : index < 1318016 then
      exact segment_sound _ 1317888 128 Restriction2574_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1318016 128 Restriction2574_1_checked index (by omega) (by omega)
  else
    if cut : index < 1318272 then
      exact segment_sound _ 1318144 128 Restriction2574_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1318272 128 Restriction2574_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
