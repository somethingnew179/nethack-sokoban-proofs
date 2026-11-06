import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1943_0_checked : (List.range' 994816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1943_1_checked : (List.range' 994944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1943_2_checked : (List.range' 995072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1943_3_checked : (List.range' 995200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1943_range (index : Nat) (lower : 994816 ≤ index) (upper : index < 995328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 995072 then
    if cut : index < 994944 then
      exact segment_sound _ 994816 128 Restriction1943_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 994944 128 Restriction1943_1_checked index (by omega) (by omega)
  else
    if cut : index < 995200 then
      exact segment_sound _ 995072 128 Restriction1943_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 995200 128 Restriction1943_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
