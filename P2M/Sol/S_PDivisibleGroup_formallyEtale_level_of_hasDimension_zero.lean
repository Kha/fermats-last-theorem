import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension
import Theorems.Thm_HopfAlgebra_formallyUnramified_of_isIdempotentElem_ker_counit
import P2M.Util
namespace P2MW.S_PDivisibleGroup_formallyEtale_level_of_hasDimension_zero

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (hG : G.HasDimension 0) (v : ℕ) :
    Algebra.FormallyEtale R (G.level v) := by

  obtain ⟨e⟩ := hG v
  haveI : Subsingleton (G.Cotangent v) := e.toEquiv.subsingleton
  have hI : IsIdempotentElem (RingHom.ker (Bialgebra.counitAlgHom R (G.level v))) :=
    (Ideal.cotangent_subsingleton_iff _).1 (inferInstanceAs (Subsingleton (G.Cotangent v)))
  haveI : Algebra.FormallyUnramified R (G.level v) := HopfAlgebra.formallyUnramified_of_isIdempotentElem_ker_counit hI

  haveI : Module.FinitePresentation R (G.level v) := Module.finitePresentation_of_projective R _
  haveI : Algebra.FinitePresentation R (G.level v) := Algebra.FinitePresentation.of_finitePresentation R _
  haveI : Algebra.Etale R (G.level v) := Algebra.Etale.of_formallyUnramified_of_flat
  infer_instance
