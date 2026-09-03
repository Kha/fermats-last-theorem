import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt

set_option autoImplicit false

universe u

theorem solution
    (O : Type u) [CommRing O] [IsNoetherianRing O] (C : Type u) [CommRing C] [Algebra O C] [Module.Finite O C] [Module.Flat O C]
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Algebra.IsUnramifiedAt O Q) :
    Algebra.Etale O C := by
  haveI : Algebra.FinitePresentation O C := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI : Algebra.FormallyUnramified O C :=
    Algebra.formallyUnramified_iff_forall.mpr fun q => h q.asIdeal
  exact Algebra.Etale.of_formallyUnramified_of_flat
