import EggeMansour

/-!
Run `lake env lean EggeMansour/Audit.lean` after building the project.
Every line should report only the standard Lean logical axioms:
`propext`, `Classical.choice`, and `Quot.sound` (or a subset).
-/

#print axioms EggeMansour.WeightedRecurrence.toUniform
#print axioms EggeMansour.UniformRecurrence.eq_of_units
#print axioms EggeMansour.UniformRecurrence.matrix_identity
#print axioms EggeMansour.UniformRecurrence.matrix_riccati
#print axioms EggeMansour.UniformRecurrence.eq_interpolant
#print axioms EggeMansour.UniformRecurrence.generic_symmetry
#print axioms EggeMansour.Universal.fieldNode_injective
#print axioms EggeMansour.Universal.uniform_symmetry_of_generic
#print axioms EggeMansour.recurrenceImpliesSymmetry
#print axioms EggeMansour.weighted_recurrence_symmetry

-- Definition-based combinatorial infrastructure (intermediate results).
#print axioms EggeMansour.Combinatorics.coeff_coeff_avoiderSeries
#print axioms EggeMansour.Combinatorics.two_mul_twoCycles
#print axioms EggeMansour.Combinatorics.twoCycles_wrap
#print axioms EggeMansour.Combinatorics.contains_directSum_iff_of_indecomposable
#print axioms EggeMansour.Combinatorics.contains_directSum_sumPatterns_iff
#print axioms EggeMansour.Combinatorics.guibert_split
#print axioms EggeMansour.Combinatorics.fixedFirstEquiv
#print axioms EggeMansour.Combinatorics.pairedFirstEquiv
#print axioms EggeMansour.Combinatorics.contains_wrap_directSum_iff
#print axioms EggeMansour.Combinatorics.definitionBasedSymmetry_of_weightedRecurrence
#print EggeMansour.Combinatorics.DefinitionBasedSymmetry
#print EggeMansour.Combinatorics.definitionBasedSymmetry_of_weightedRecurrence

-- Complete results: no recurrence, counting or symmetry premise remains.
#print axioms EggeMansour.Combinatorics.listWeightedIdentity
#print axioms EggeMansour.Combinatorics.combinatorialWeightedRecurrence
#print axioms EggeMansour.Combinatorics.definitionBasedSymmetry
#print axioms EggeMansour.Combinatorics.wrappedSeries_eq_reducedSeries
#print axioms EggeMansour.Combinatorics.reducedWeightedRecurrence
#print axioms EggeMansour.Combinatorics.patternSeries_reorder
#print axioms EggeMansour.Combinatorics.avoiderCount_reorder
#print axioms EggeMansour.Combinatorics.layeredSeries_reorder
#print axioms EggeMansour.Combinatorics.layeredCount_reorder
#check EggeMansour.Combinatorics.definitionBasedSymmetry
#check EggeMansour.Combinatorics.reducedWeightedRecurrence
#check EggeMansour.Combinatorics.layeredCount_reorder
