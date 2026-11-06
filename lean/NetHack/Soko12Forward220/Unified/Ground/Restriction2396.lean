import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2396_0_checked : (List.range' 1226752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2396_1_checked : (List.range' 1226880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2396_2_checked : (List.range' 1227008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2396_3_checked : (List.range' 1227136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2396_range (index : Nat) (lower : 1226752 ≤ index) (upper : index < 1227264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1227008 then
    if cut : index < 1226880 then
      exact segment_sound _ 1226752 128 Restriction2396_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1226880 128 Restriction2396_1_checked index (by omega) (by omega)
  else
    if cut : index < 1227136 then
      exact segment_sound _ 1227008 128 Restriction2396_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1227136 128 Restriction2396_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
