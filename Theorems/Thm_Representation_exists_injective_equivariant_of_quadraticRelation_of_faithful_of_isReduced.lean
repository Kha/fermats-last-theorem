import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced

set_option autoImplicit false

theorem Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [IsReduced R]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (hV : Module.finrank R V = 2)
    (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    [Module.Finite 𝒪 Y] [Module.IsTorsionFree 𝒪 Y]
    (hfaith : ∀ x : R, (∀ y : Y, x • y = 0) → x = 0)
    (ρY : G →* Module.End R Y)
    {Δ : Type} [CommGroup Δ] [Finite Δ] (D : Δ →* Module.End R Y)
    (hD : ∀ (d : Δ) (g : G), D d * ρY g = ρY g * D d)
    (δ : G →* Δ) (c : G →* Rˣ)
    (hrel : ∀ g : G,
      ρY g * ρY g - (LinearMap.trace R V (ρV g)) • ρY g + ((c g : Rˣ) : R) • D (δ g) = 0) :
    ∃ j : V →ₗ[R] Y, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρY g (j v) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced.solution
