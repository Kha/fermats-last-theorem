import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation

set_option autoImplicit false

theorem Module.exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [IsReduced R]
    {G : Type} [Group G]
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    [Module.Finite 𝒪 Y] [Module.IsTorsionFree 𝒪 Y]
    (hfaith : ∀ x : R, (∀ y : Y, x • y = 0) → x = 0)
    (ρY : G →* Module.End R Y)
    {Δ : Type} [CommGroup Δ] [Finite Δ] (D : Δ →* Module.End R Y)
    (hD : ∀ (d : Δ) (g : G), D d * ρY g = ρY g * D d)
    (δ : G →* Δ) (c : G →* Rˣ) (t : G → R)
    (hrel : ∀ g : G, ρY g * ρY g - (t g) • ρY g + ((c g : Rˣ) : R) • D (δ g) = 0) :
    ∃ (k : Type) (_ : CommRing k) (_ : IsArtinianRing k) (_ : IsReduced k) (_ : Algebra ℚ k)
      (_ : Algebra R k) (_ : Algebra 𝒪 k) (_ : IsScalarTower 𝒪 R k)
      (_ : Function.Injective (algebraMap R k))
      (_ : ∀ a : 𝒪, a ≠ 0 → IsUnit (algebraMap 𝒪 k a))
      (M : Type) (_ : AddCommGroup M) (_ : Module k M) (_ : Module R M) (_ : Module 𝒪 M)
      (_ : IsScalarTower R k M) (_ : IsScalarTower 𝒪 k M) (_ : IsScalarTower 𝒪 R M) (_ : Module.Finite k M)
      (_ : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
      (ρM : G →* Module.End k M) (dM : G →* kˣ)
      (_ : ∀ g : G, ρM g * ρM g - (algebraMap R k (t g)) • ρM g + ((dM g : kˣ) : k) • (1 : Module.End k M) = 0)
      (ι : Y →ₗ[R] M) (_ : Function.Injective ι)
      (_ : ∀ (g : G) (y : Y), ι (ρY g y) = ρM g (ι y)),
      ∀ m : M, ∃ a : 𝒪, a ≠ 0 ∧ a • m ∈ LinearMap.range ι := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation.solution
