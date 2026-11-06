import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1925_0_checked : (List.range' 985600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1925_1_checked : (List.range' 985728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1925_2_checked : (List.range' 985856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1925_3_checked : (List.range' 985984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1925_range (index : Nat) (lower : 985600 ≤ index) (upper : index < 986112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 985856 then
    if cut : index < 985728 then
      exact segment_sound _ 985600 128 Restriction1925_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 985728 128 Restriction1925_1_checked index (by omega) (by omega)
  else
    if cut : index < 985984 then
      exact segment_sound _ 985856 128 Restriction1925_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 985984 128 Restriction1925_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
