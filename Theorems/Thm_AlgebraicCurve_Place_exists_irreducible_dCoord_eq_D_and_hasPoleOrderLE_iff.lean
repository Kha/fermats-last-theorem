import Mathlib
import Definitions.Def_AlgebraicCurve_LogDeRhamH1
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff

set_option autoImplicit false
open KaehlerDifferential

theorem AlgebraicCurve.Place.exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ π : v.toValuationSubring, Irreducible π ∧
      v.dCoord = KaehlerDifferential.D K F (π : F) ∧
      (∀ (n : ℕ) (ω : Ω[F⁄K]), v.HasPoleOrderLE n ω ↔
        ∃ f : F, (π : F) ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord) ∧
      (∀ (n : ℕ) (g : F), v.FnPoleOrderLE n g ↔ (π : F) ^ n * g ∈ v.toValuationSubring) ∧
      (∀ (ω : Ω[F⁄K]) (a : K), v.HasLogResidue ω a ↔
        ∃ f : F, ω = f • v.dCoord ∧ v.HasValue ((π : F) * f) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff.solution
