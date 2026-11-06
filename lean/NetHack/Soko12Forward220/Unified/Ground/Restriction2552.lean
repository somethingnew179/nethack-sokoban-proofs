import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2552_0_checked : (List.range' 1306624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2552_1_checked : (List.range' 1306752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2552_2_checked : (List.range' 1306880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2552_3_checked : (List.range' 1307008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2552_range (index : Nat) (lower : 1306624 ≤ index) (upper : index < 1307136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1306880 then
    if cut : index < 1306752 then
      exact segment_sound _ 1306624 128 Restriction2552_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1306752 128 Restriction2552_1_checked index (by omega) (by omega)
  else
    if cut : index < 1307008 then
      exact segment_sound _ 1306880 128 Restriction2552_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1307008 128 Restriction2552_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
