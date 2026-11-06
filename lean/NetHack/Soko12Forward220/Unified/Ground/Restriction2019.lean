import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2019_0_checked : (List.range' 1033728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2019_1_checked : (List.range' 1033856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2019_2_checked : (List.range' 1033984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2019_3_checked : (List.range' 1034112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2019_range (index : Nat) (lower : 1033728 ≤ index) (upper : index < 1034240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1033984 then
    if cut : index < 1033856 then
      exact segment_sound _ 1033728 128 Restriction2019_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1033856 128 Restriction2019_1_checked index (by omega) (by omega)
  else
    if cut : index < 1034112 then
      exact segment_sound _ 1033984 128 Restriction2019_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1034112 128 Restriction2019_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
