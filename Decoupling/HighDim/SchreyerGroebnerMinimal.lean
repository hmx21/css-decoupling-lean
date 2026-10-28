import Decoupling.HighDim.SchreyerGroebnerDivision

/-!
# Minimal Gröbner leading terms are inherited from every Gröbner family

This transfers leading-exponent restrictions without assuming homogeneity.
It concerns proved mathematical minimal bases, not a runtime deletion algorithm.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
variable {K : Type*} [Field K] {D r s n : ℕ}
variable {o : ModuleOrder D r} {G : Fin s → Vec K D r} {H : Fin n → Vec K D r}
  {N : Submodule (Poly K D) (Vec K D r)}

/-- Each minimal leading term equals a leading term in any other GB of the same actual module. -/
theorem minimal_leading_eq_some (hG : IsGroebnerBasis o G N)
    (hH : IsGroebnerBasis o H N) (hmin : IsMinimal o H)
    (i : Fin n) (t : Term D r) (ht : IsLeading o (H i) t) :
    ∃ j u,IsLeading o (G j) u ∧ t=u := by
  obtain ⟨j,u,hj,hut⟩ := hG.leading (H i) (hH.mem i) t ht
  obtain ⟨k,v,hk,hvu⟩ := hH.leading (G j) (hG.mem j) u hj
  have hki : k=i := hmin.minimal k i v t hk ht (divides_trans hvu hut)
  subst k
  have hvt : v=t := isLeading_unique o hk ht
  subst v
  exact ⟨j,u,hj,Prod.ext (le_antisymm hvu.2 hut.2) hvu.1⟩

/-- Any predicate on leading module terms passes from a GB to a minimal GB. -/
theorem minimal_leading_property (hG : IsGroebnerBasis o G N)
    (hH : IsGroebnerBasis o H N) (hmin : IsMinimal o H)
    (P : Term D r → Prop) (hP : ∀ j u,IsLeading o (G j) u → P u) :
    ∀ i t,IsLeading o (H i) t → P t := by
  intro i t ht
  obtain ⟨j,u,hj,he⟩ := minimal_leading_eq_some hG hH hmin i t ht
  rw [he]
  exact hP j u hj

end
end Decoupling.HighDim.SchreyerModule
