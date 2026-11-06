import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1175_0_checked : (List.range' 601600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1175_1_checked : (List.range' 601728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1175_2_checked : (List.range' 601856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1175_3_checked : (List.range' 601984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1175_range (index : Nat) (lower : 601600 ≤ index) (upper : index < 602112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 601856 then
    if cut : index < 601728 then
      exact segment_sound _ 601600 128 Restriction1175_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 601728 128 Restriction1175_1_checked index (by omega) (by omega)
  else
    if cut : index < 601984 then
      exact segment_sound _ 601856 128 Restriction1175_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 601984 128 Restriction1175_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
