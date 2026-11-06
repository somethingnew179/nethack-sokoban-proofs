import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1185_0_checked : (List.range' 606720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1185_1_checked : (List.range' 606848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1185_2_checked : (List.range' 606976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1185_3_checked : (List.range' 607104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1185_range (index : Nat) (lower : 606720 ≤ index) (upper : index < 607232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 606976 then
    if cut : index < 606848 then
      exact segment_sound _ 606720 128 Restriction1185_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 606848 128 Restriction1185_1_checked index (by omega) (by omega)
  else
    if cut : index < 607104 then
      exact segment_sound _ 606976 128 Restriction1185_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 607104 128 Restriction1185_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
