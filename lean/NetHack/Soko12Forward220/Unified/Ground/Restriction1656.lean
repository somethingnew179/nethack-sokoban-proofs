import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1656_0_checked : (List.range' 847872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1656_1_checked : (List.range' 848000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1656_2_checked : (List.range' 848128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1656_3_checked : (List.range' 848256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1656_range (index : Nat) (lower : 847872 ≤ index) (upper : index < 848384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 848128 then
    if cut : index < 848000 then
      exact segment_sound _ 847872 128 Restriction1656_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 848000 128 Restriction1656_1_checked index (by omega) (by omega)
  else
    if cut : index < 848256 then
      exact segment_sound _ 848128 128 Restriction1656_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 848256 128 Restriction1656_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
