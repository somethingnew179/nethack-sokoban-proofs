import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2320_0_checked : (List.range' 1187840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2320_1_checked : (List.range' 1187968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2320_2_checked : (List.range' 1188096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2320_3_checked : (List.range' 1188224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2320_range (index : Nat) (lower : 1187840 ≤ index) (upper : index < 1188352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1188096 then
    if cut : index < 1187968 then
      exact segment_sound _ 1187840 128 Restriction2320_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1187968 128 Restriction2320_1_checked index (by omega) (by omega)
  else
    if cut : index < 1188224 then
      exact segment_sound _ 1188096 128 Restriction2320_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1188224 128 Restriction2320_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
