import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

def frobAlgHomTwist (k₀ : Type) [CommRing k₀] (r : ℕ) [Fact r.Prime] (C : Type) [CommRing C] [CharP C r]
    (c : k₀ →+* C) :
    @AlgHom k₀ C C _ _ _ c.toAlgebra ((frobenius C r).comp c).toAlgebra :=
  @AlgHom.mk k₀ C C _ _ _ c.toAlgebra ((frobenius C r).comp c).toAlgebra (frobenius C r) (fun _ => rfl)

theorem solution
    {k₀ : Type} [CommRing k₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k₀)}
    {L : RelativeGroupLaw k₀ f} {g : ℕ} {F : MvFormalGroup g k₀} {θ : RelativeGroupLaw.FormalCoordinates f g}
    (hθ : L.IsFormalCoordinates F θ)
    (r : ℕ) [Fact r.Prime] (C : Type) [CommRing C] [CharP C r] (c : k₀ →+* C)
    (s : Fin g → C) (hs : ∀ i, IsNilpotent (s i)) :
    (@θ C _ ((frobenius C r).comp c).toAlgebra (fun i => s i ^ r)).1 =
      Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ (@θ C _ c.toAlgebra s).1 := by
  obtain ⟨hnat, -⟩ := hθ
  have key := @hnat C _ c.toAlgebra C _ ((frobenius C r).comp c).toAlgebra (frobAlgHomTwist k₀ r C c) s hs
  have hφs : ((frobAlgHomTwist k₀ r C c) ∘ s : Fin g → C) = fun i => s i ^ r := by
    funext i
    show frobenius C r (s i) = s i ^ r
    rfl
  rw [hφs] at key
  rw [key]
  rfl
