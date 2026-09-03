import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible

set_option autoImplicit false

theorem Representation.injective_liftBaseChange_of_isAbsolutelyIrreducible
    {F k G V W : Type} [Field F] [Field k] [Algebra F k] [Group G]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower F k W]
    (ρ : Representation F G V) [Representation.IsAbsolutelyIrreducible.{0} ρ]
    (τ : Representation k G W)
    (ι : V →ₗ[F] W) (hι : Function.Injective ι)
    (hιG : ∀ (g : G) (v : V), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k) := by p2m_exact_reverting @_root_.P2MW.S_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible.solution
