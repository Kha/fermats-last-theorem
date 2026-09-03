import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension

set_option autoImplicit false

theorem AlgebraicCurve.cartier_map_eq_map_cartier_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [PerfectField K] [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (C' : Ω[F'⁄K'] →+ Ω[F'⁄K'])
    (hsemi' : ∀ (f : F') (ω : Ω[F'⁄K']), C' (f ^ p • ω) = f • C' ω)
    (hker' : ∀ f : F', C' (KaehlerDifferential.D K' F' f) = 0)
    (hlog' : ∀ f : F', C' (f ^ (p - 1) • KaehlerDifferential.D K' F' f) = KaehlerDifferential.D K' F' f) :
    ∀ ω : Ω[F⁄K], C' (KaehlerDifferential.map K K' F F' ω) = KaehlerDifferential.map K K' F F' (C ω) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension.solution
