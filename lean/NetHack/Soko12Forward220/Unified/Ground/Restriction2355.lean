import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2355_0_checked : (List.range' 1205760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2355_1_checked : (List.range' 1205888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2355_2_checked : (List.range' 1206016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2355_3_checked : (List.range' 1206144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2355_range (index : Nat) (lower : 1205760 ≤ index) (upper : index < 1206272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1206016 then
    if cut : index < 1205888 then
      exact segment_sound _ 1205760 128 Restriction2355_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1205888 128 Restriction2355_1_checked index (by omega) (by omega)
  else
    if cut : index < 1206144 then
      exact segment_sound _ 1206016 128 Restriction2355_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1206144 128 Restriction2355_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
