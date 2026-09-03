import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_sqZero_of_natCast_eq_zero
    {R₀ : Type u} [CommRing R₀]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R₀)} (G : RelativeGroupLaw R₀ f)
    (ℓ : ℕ) (R' S' : CommRingCat.{u}) [IsLocalRing R'] (φ : R' ⟶ S') (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥) (hℓ : (ℓ : R') = 0)
    (t : Spec R' ⟶ Spec (CommRingCat.of R₀)) (x : SchemeHomOver t f)
    (hx : GoodReductionJacobian.schemeHomOverComp (Spec.map φ) rfl x = G.one (Spec.map φ ≫ t)) :
    G.nsmul t ℓ x = G.one t := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero.solution
