import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1196_0_checked : (List.range' 612352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1196_1_checked : (List.range' 612480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1196_2_checked : (List.range' 612608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1196_3_checked : (List.range' 612736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1196_range (index : Nat) (lower : 612352 ≤ index) (upper : index < 612864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 612608 then
    if cut : index < 612480 then
      exact segment_sound _ 612352 128 Restriction1196_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 612480 128 Restriction1196_1_checked index (by omega) (by omega)
  else
    if cut : index < 612736 then
      exact segment_sound _ 612608 128 Restriction1196_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 612736 128 Restriction1196_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
