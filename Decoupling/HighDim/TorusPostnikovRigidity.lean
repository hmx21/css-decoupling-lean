import Decoupling.HighDim.TorusPostnikov
import Decoupling.HighDim.TwoLayerFormality

/-!
# Equality rigidity for the actual Postnikov long exact sequences

This categorical lemma isolates the detection input that will be proved
by native Koszul Yoneda composition. It is applied only after lower
truncations have been proved formal by induction. No splitting of a
lower truncation or vanishing of an attachment is presumed.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits
open PostnikovTruncation PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Purely categorical induction: if morphisms between the permitted
single layers are detected by a representable functor, equality in its
Postnikov bound forces the entire genuine object to be formal. -/
theorem postnikov_formal_of_maximal
    (P : Derived K D) (Q : ModuleCat (Laurent K D) → Prop)
    (hIso : ∀ {A B}, (A ≅ B) → Q A → Q B)
    (hFinite : ∀ A (i : ℤ), Q A → 1 ≤ i → i < D →
      Module.Finite K (homCoefficients P
        ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)))
    (hDetect : ∀ A B (i j : ℤ), Q A → Q B → 1 ≤ i → i < j → j < D →
      ∀ f : (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj A ⟶
        ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj B)⟦(1 : ℤ)⟧,
        (∀ g : P ⟶ _, g ≫ f = 0) → f = 0) :
    ∀ (s : Finset ℤ) (X : Derived K D), Supported X s →
      (∀ i ∈ s, 1 ≤ i ∧ i < D) → (∀ i ∈ s, Q (H X i)) →
      Module.finrank K (homCoefficients P X) =
        ∑ i ∈ s, Module.finrank K (representedLayer P X i) →
      Nonempty (X ≅ TwoLayer.homologySum X s) := by
  intro s
  refine Finset.strongInductionOn s (fun s ih => ?_)
  intro X hX hdeg hQ heq
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hle : ∀ i ∈ s, i ≤ j := fun i hi => Finset.le_max' s i hi
    have hlt : ∀ i ∈ s.erase j, i < j := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      have := hle i hi'.2
      omega
    have : X.IsLE j := supported_isLE hX j hle
    have hF : ∀ i ∈ s, Module.Finite K (representedLayer P X i) :=
      fun i hi => hFinite (H X i) i (hQ i hi) (hdeg i hi).1 (hdeg i hi).2
    have he (i : ℤ) (hi : i ∈ s.erase j) :
        representedLayer P (lower X j) i ≅ representedLayer P X i :=
      homCoefficientsIso P ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).mapIso
        (lowerHomologyIso X j i (hlt i hi)))
    have hFL : ∀ i ∈ s.erase j, Module.Finite K (representedLayer P (lower X j) i) := by
      intro i hi
      let := hF i (Finset.mem_of_mem_erase hi)
      exact Module.Finite.equiv (he i hi).symm.toLinearEquiv
    obtain ⟨hLF, hLB⟩ := postnikov_finrank_le P (s.erase j) (lower X j)
      (lower_supported hX j) hFL
    let := hLF
    let := hF j hj
    let eU : homCoefficients P (upper X j) ≅ representedLayer P X j :=
      homCoefficientsIso P (upperSingleIso X j)
    let : Module.Finite K (homCoefficients P (upper X j)) :=
      Module.Finite.equiv eU.symm.toLinearEquiv
    let : Module.Finite K (homCoefficients P (triangle X j).obj₁) := hLF
    let : Module.Finite K (homCoefficients P (triangle X j).obj₃) := by
      change Module.Finite K (homCoefficients P (upper X j))
      infer_instance
    have hT := t.triangleLTGE_distinguished j X
    have hb := triangle_finrank_le P (triangle X j) hT
    change Module.finrank K (homCoefficients P X) ≤
      Module.finrank K (homCoefficients P (lower X j)) +
        Module.finrank K (homCoefficients P (upper X j)) at hb
    have hsums : (∑ i ∈ s.erase j, Module.finrank K (representedLayer P (lower X j) i)) =
        ∑ i ∈ s.erase j, Module.finrank K (representedLayer P X i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (he i hi).toLinearEquiv.finrank_eq
    have heq' := heq
    rw [← Finset.sum_erase_add _ _ hj, ← hsums,
      ← eU.toLinearEquiv.finrank_eq] at heq'
    have hLowerEq : Module.finrank K (homCoefficients P (lower X j)) =
        ∑ i ∈ s.erase j, Module.finrank K (representedLayer P (lower X j) i) := by omega
    obtain ⟨eL⟩ := ih (s.erase j) (Finset.erase_ssubset hj) (lower X j)
      (lower_supported hX j) (fun i hi => hdeg i (Finset.mem_of_mem_erase hi))
      (fun i hi => hIso (lowerHomologyIso X j i (hlt i hi)).symm
        (hQ i (Finset.mem_of_mem_erase hi))) hLowerEq
    have hδ : postcompose P (triangle X j).mor₃ = 0 := by
      by_contra hn
      have hstrict := triangle_finrank_lt P (triangle X j) hT hn
      change Module.finrank K (homCoefficients P X) <
        Module.finrank K (homCoefficients P (lower X j)) +
          Module.finrank K (homCoefficients P (upper X j)) at hstrict
      omega
    let B := fun i : s.erase j =>
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj (H X i)
    let eLower : lower X j ≅ ⨁ B := eL ≪≫ biproduct.mapIso (fun i =>
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).mapIso
        (lowerHomologyIso X j i (hlt i i.property)))
    have hzero : (triangle X j).mor₃ = 0 := by
      apply (cancel_mono (eLower.hom⟦(1 : ℤ)⟧')).mp
      have hh := PostnikovStep.map_eq_zero_of_components (𝟭 (Derived K D)) B 1
        ((triangle X j).mor₃ ≫ eLower.hom⟦(1 : ℤ)⟧') (by
          intro i
          simp only [Functor.id_map, Category.assoc]
          apply (cancel_epi (upperSingleIso X j).inv).mp
          have hf := hDetect (H X j) (H X i) i j (hQ j hj)
            (hQ i (Finset.mem_of_mem_erase i.property))
            (hdeg i (Finset.mem_of_mem_erase i.property)).1 (hlt i i.property) (hdeg j hj).2
            ((upperSingleIso X j).inv ≫ (triangle X j).mor₃ ≫
              eLower.hom⟦(1 : ℤ)⟧' ≫ (biproduct.π B i)⟦(1 : ℤ)⟧') (by
                intro g
                have hg := congrArg (fun f => f (g ≫ (upperSingleIso X j).inv)) hδ
                change (g ≫ (upperSingleIso X j).inv) ≫ (triangle X j).mor₃ = 0 at hg
                rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hg, zero_comp, zero_comp])
          simpa only [Category.assoc, comp_zero] using hf)
      simpa only [Functor.id_map, zero_comp] using hh
    obtain ⟨es, _, _⟩ := (Triangles.connecting_eq_zero_iff_compatible_biproduct
      (triangle X j) hT).mp hzero
    exact ⟨es.symm ≪≫ biprod.mapIso eLower (upperSingleIso X j) ≪≫
      FiniteBiproduct.eraseIso
        (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj (H X i)) s j hj⟩
  · exact TwoLayer.formal_of_card_le_one X s hX (by
      rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp)

end
end Decoupling.HighDim.Torus
