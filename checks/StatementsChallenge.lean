/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIIChallenge
set_option pp.all true
set_option pp.universes true
#print TypedTriangle.Host
#print TypedTriangle.triEdges
#print TypedTriangle.edges
#print TypedTriangle.IsAllowed
#print TypedTriangle.IsDecomposition
#print STS.IsSTS
#print CDRBicolour.Absorption.nbL
#print CDRBicolour.Absorption.degL
#print CDRBicolour.KBicolor.bicF
#print CDRBicolour.KBicolor.kHost
#print CDRBicolour.KBicolor.ksz
#print CDRBicolour.KBicolor.kTypeCount
#print CDRBicolour.KBicolor.kBlocks
#print CDRBicolour.KBicolor.TypeCoord
#print CDRBicolour.KBicolor.typeVector
#print CDRBicolour.KBicolor.exactTypeFibre
#print CDRBicolour.KBicolor.exactTypeCount
#print TypedTriangle.Pasch.IsPasch
#print TypedTriangle.Pasch.decidableIsPasch
#print TypedTriangle.Pasch.configurations
#print TypedTriangle.Pasch.count
#print CDRBicolour.PaperIII.IsSTS
#print CDRBicolour.PaperIII.IsBicolouring
#print CDRBicolour.PaperIII.Bicolourable
#print CDRBicolour.PaperIII.Admissible
#check @CDRBicolour.KBicolor.kbicolour_completion_types_exact
#print axioms CDRBicolour.KBicolor.kbicolour_completion_types_exact
#check @CDRBicolour.KBicolor.optimal_prescribed_type_count_of_three_le
#print axioms CDRBicolour.KBicolor.optimal_prescribed_type_count_of_three_le
#check @CDRBicolour.KBicolor.kbicolour_types_exact_many_pasch_counts
#print axioms CDRBicolour.KBicolor.kbicolour_types_exact_many_pasch_counts
#check @CDRBicolour.PaperIII.bicolourable_eventually_unconditional
#print axioms CDRBicolour.PaperIII.bicolourable_eventually_unconditional
