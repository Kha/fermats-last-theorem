import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators MonoidalCategory

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
    {g d n : ℕ} (δ : Fin g → ℕ) {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    (hu : PolarisedAbelianScheme.IsOfType δ u)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y →
      ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    {L : Type} [Field L] (ψ : K →+* L)
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f)
    (hy : Polarisation.MemKernel u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t) y) :
    ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y.1 = Spec.map (CommRingCat.ofHom ψ) ≫ (x h).1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed.solution
