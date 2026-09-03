import Mathlib
import Theorems.Thm_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
import P2M.Util
namespace P2MW.S_Algebra_Etale_of_formallyUnramified_residueField_baseChange
open scoped TensorProduct

theorem solution (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.Etale R S := by
  haveI := Algebra.FormallyUnramified.of_residueField_baseChange_of_finite R S h
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
  haveI : Algebra.FinitePresentation R S := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat
