import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sub_C_mem_eisensteinIdeal

open ModularCurve

theorem ModularCurve.exists_sub_C_mem_eisensteinIdeal (N : ℕ) (t : HeckeAlg) : ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sub_C_mem_eisensteinIdeal.solution
