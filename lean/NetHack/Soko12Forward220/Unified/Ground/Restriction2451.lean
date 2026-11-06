import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2451_0_checked : (List.range' 1254912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2451_1_checked : (List.range' 1255040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2451_2_checked : (List.range' 1255168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2451_3_checked : (List.range' 1255296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2451_range (index : Nat) (lower : 1254912 ≤ index) (upper : index < 1255424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1255168 then
    if cut : index < 1255040 then
      exact segment_sound _ 1254912 128 Restriction2451_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1255040 128 Restriction2451_1_checked index (by omega) (by omega)
  else
    if cut : index < 1255296 then
      exact segment_sound _ 1255168 128 Restriction2451_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1255296 128 Restriction2451_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
