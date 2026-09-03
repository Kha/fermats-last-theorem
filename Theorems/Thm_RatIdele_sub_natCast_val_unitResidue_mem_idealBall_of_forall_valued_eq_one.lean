import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import P2M.Util
import P2M.Sol.S_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem RatIdele.sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
    (M : ℕ) [NeZero M] (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) :
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ)
        - ((RatIdele.unitResidue M (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) u)).val : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ NumberField.AdelicLevel.idealBall (𝓞 ℚ) ℚ (Ideal.span {((M : ℕ) : 𝓞 ℚ)}) := by p2m_exact_reverting @_root_.P2MW.S_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one.solution
