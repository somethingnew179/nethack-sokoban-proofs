import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1425_0_checked : (List.range' 729600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1425_1_checked : (List.range' 729728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1425_2_checked : (List.range' 729856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1425_3_checked : (List.range' 729984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1425_range (index : Nat) (lower : 729600 ≤ index) (upper : index < 730112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 729856 then
    if cut : index < 729728 then
      exact segment_sound _ 729600 128 Restriction1425_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 729728 128 Restriction1425_1_checked index (by omega) (by omega)
  else
    if cut : index < 729984 then
      exact segment_sound _ 729856 128 Restriction1425_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 729984 128 Restriction1425_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
