import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.val_apply_pow_eq_specMap_frobenius_comp_val_apply
    {k₀ : Type} [CommRing k₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k₀)}
    {L : RelativeGroupLaw k₀ f} {g : ℕ} {F : MvFormalGroup g k₀} {θ : RelativeGroupLaw.FormalCoordinates f g}
    (hθ : L.IsFormalCoordinates F θ)
    (r : ℕ) [Fact r.Prime] (C : Type) [CommRing C] [CharP C r] (c : k₀ →+* C)
    (s : Fin g → C) (hs : ∀ i, IsNilpotent (s i)) :
    (@θ C _ ((frobenius C r).comp c).toAlgebra (fun i => s i ^ r)).1 =
      Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ (@θ C _ c.toAlgebra s).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply.solution
