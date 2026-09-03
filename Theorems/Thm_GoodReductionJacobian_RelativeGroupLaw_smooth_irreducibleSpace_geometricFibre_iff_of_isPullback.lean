import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_isPullback

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
    {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R')
    {Z Z' : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R)) (f' : Z' ⟶ Spec (CommRingCat.of R'))
    (gZ : Z' ⟶ Z) (hpb : IsPullback gZ f' f (Spec.map (CommRingCat.ofHom ψ)))
    (g : ℕ) (k : Type) [CommRing k] (x' : R' →+* k) :
    (Smooth (pullback.snd f' (Spec.map (CommRingCat.ofHom x'))) ∧
        IrreducibleSpace ↥(pullback f' (Spec.map (CommRingCat.ofHom x'))) ∧
        topologicalKrullDim ↥(pullback f' (Spec.map (CommRingCat.ofHom x'))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f' (Spec.map (CommRingCat.ofHom x'))))) ↔
    (Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom (x'.comp ψ)))))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_isPullback.solution
