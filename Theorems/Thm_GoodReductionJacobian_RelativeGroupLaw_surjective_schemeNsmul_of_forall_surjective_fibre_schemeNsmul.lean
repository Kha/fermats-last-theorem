import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ)
    (hfib : ∀ s : (Spec (CommRingCat.of R) : Scheme.{u}), Surjective ((G.fibre s).schemeNsmul n)) :
    Surjective (G.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul.solution
