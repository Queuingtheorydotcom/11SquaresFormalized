import ElevenSquare.Interop.Wand125.Coverage
import ElevenSquare

-- These targets are expected to have only the standard axioms.
#print axioms ElevenSquare.construction_packable
#print axioms ElevenSquare.Pending.recorded_cases_exact
#print axioms ElevenSquare.Pending.overlay_inventory_complete
#print axioms ElevenSquare.Pending.d4_forces_case438
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached.certificate
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.certificate
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.certificate
#print axioms ElevenSquare.Tasks.T02.Prior1000Step001.case1000_after_integer_second_step
#print axioms ElevenSquare.Tasks.T02.Prior1000Step001.case1000_after_archived_second_step
#print axioms ElevenSquare.Pending.exact_local_packet_exists
#print axioms ElevenSquare.Pending.construction_locally_isolated

-- Newly wired families: these queries must be clean; full replay is still pending.
#print axioms ElevenSquare.Pending.baseline_certificate_exists
#print axioms ElevenSquare.Pending.baseline_excluded
#print axioms ElevenSquare.Pending.prior_certificate_exists
#print axioms ElevenSquare.Pending.prior_excluded
#print axioms SquarePacking.S11Opt.Split.field_excluded
#print axioms SquarePacking.S11Opt.Split.generic_excluded
#print axioms SquarePacking.S11Opt.Split.prior_excluded

-- These targets still depend on the explicit remaining admissions.
#print axioms ElevenSquare.Pending.returned_certificate_exists
#print axioms ElevenSquare.Pending.global_lower_bound
#print axioms ElevenSquare.optimal_side_lower_bound
#print axioms ElevenSquare.optimality

#print axioms ElevenSquare.Interop.Wand125.packable_eleven_iff
#print axioms ElevenSquare.Interop.Wand125.excludes_occupancy
#print axioms ElevenSquare.Interop.Wand125.certificate
#print axioms SquarePacking.S11Opt.ImportedFields.applicable_sound

#print axioms ElevenSquare.Interop.Wand125.new_case_excluded
#print axioms ElevenSquare.Interop.Wand125.newCases_disjoint

#print axioms ElevenSquare.Interop.Wand125.newCases_baseline
