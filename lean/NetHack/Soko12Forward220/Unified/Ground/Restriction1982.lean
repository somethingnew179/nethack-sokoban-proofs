import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1982_0_checked : (List.range' 1014784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1982_1_checked : (List.range' 1014912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1982_2_checked : (List.range' 1015040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1982_3_checked : (List.range' 1015168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1982_range (index : Nat) (lower : 1014784 ≤ index) (upper : index < 1015296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1015040 then
    if cut : index < 1014912 then
      exact segment_sound _ 1014784 128 Restriction1982_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1014912 128 Restriction1982_1_checked index (by omega) (by omega)
  else
    if cut : index < 1015168 then
      exact segment_sound _ 1015040 128 Restriction1982_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1015168 128 Restriction1982_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
