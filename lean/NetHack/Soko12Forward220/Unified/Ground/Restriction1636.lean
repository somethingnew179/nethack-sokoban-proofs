import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1636_0_checked : (List.range' 837632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1636_1_checked : (List.range' 837760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1636_2_checked : (List.range' 837888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1636_3_checked : (List.range' 838016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1636_range (index : Nat) (lower : 837632 ≤ index) (upper : index < 838144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 837888 then
    if cut : index < 837760 then
      exact segment_sound _ 837632 128 Restriction1636_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 837760 128 Restriction1636_1_checked index (by omega) (by omega)
  else
    if cut : index < 838016 then
      exact segment_sound _ 837888 128 Restriction1636_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 838016 128 Restriction1636_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
