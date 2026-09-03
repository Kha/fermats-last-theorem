import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ArchOccursInClassOf_map_starRingEnd

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.ArchOccursInClassOf.map_starRingEnd
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Θ : HeckeEigensystem F ℂ) (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop)
    (h : ArchOccursInClassOf F D Θ P) :
    ArchOccursInClassOf F D (Θ.map (starRingEnd ℂ)) (fun φ => P (fun g => (starRingEnd ℂ) (φ g))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ArchOccursInClassOf_map_starRingEnd.solution
