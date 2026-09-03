import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F,
      IsFactorizableTestFn F (fun y => f ((g * k) * y * (g * k)⁻¹)) ∧
      IsArchBiFinite F tys' (fun y => f ((g * k) * y * (g * k)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.solution
