import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry~existsUnique_specMap_mk_pow_comp_eq_of_isAdicComplete_of_isLocalRing LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

theorem CerednikDrinfeld.FormalOmega.existsUnique_hom_comp_eq_of_compatible_modPow
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (R : Type) [CommRing R] [Algebra 𝒪 R] [IsLocalRing R]
    (hR : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    {X : Scheme.{0}} (x : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ X)
    (hx : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ x (n + 1) = x n) :
    ∃! y : Spec (CommRingCat.of R) ⟶ X,
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (algebraMap R (modPow π R n))) ≫ y = x n := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_hom_comp_eq_of_compatible_modPow.solution
