import Decoupling.HighDim.GluedBinaryGeometry

/-!
# General-prime SUM locality on the original lattice

The finite coarse-cell word acts on the actual original species and sites.
The site bijection proves fine-lattice displacement, disjointness, bounded
range, and covariance of both Pauli-label actions under the retained lattice.
-/
namespace Decoupling.HighDim.GluedDirectional
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime]

abbrev FineConfig := Fin 6 → Translation 3 → ZMod p
abbrev CoarseConfig := (Fin 6 × Fin p) → Translation 3 → ZMod p

def configurationCoordinates (f : FineConfig p) : CoarseConfig p :=
  fun i a => f i.1 (inclusion p a + row p i.2)

theorem physicalSite_sub (i : Fin 6 × Fin p) (a b : Translation 3) :
    physicalSiteEquiv p (i, a - b) =
      (i.1, (physicalSiteEquiv p (i, a)).2 - inclusion p b) := by
  rcases i with ⟨i, r⟩
  simp only [physicalSiteEquiv_apply, map_sub]
  congr 1
  abel

omit [Fact p.Prime] in
theorem configurationCoordinates_translation (f : FineConfig p) (b : Translation 3) :
    configurationCoordinates p (Circuit.SUM.translateConfig (inclusion p b) f) =
      Circuit.SUM.translateConfig b (configurationCoordinates p f) := by
  funext i a
  simp only [configurationCoordinates, Circuit.SUM.translateConfig, map_sub]
  congr 1
  abel

variable (g : Circuit.SUM (ZMod p) 3 (Fin 6 × Fin p))

def fineXConfig (f : FineConfig p) (i : Fin 6) (a : Translation 3) : ZMod p :=
  let z := (physicalSiteEquiv p).symm (i, a)
  g.xConfig (configurationCoordinates p f) z.1 z.2

def fineZConfig (f : FineConfig p) (i : Fin 6) (a : Translation 3) : ZMod p :=
  let z := (physicalSiteEquiv p).symm (i, a)
  g.zConfig (configurationCoordinates p f) z.1 z.2

@[simp] theorem fineXConfig_atSite (f : FineConfig p) (i : Fin 6 × Fin p) (a : Translation 3) :
    fineXConfig p g f (physicalSiteEquiv p (i, a)).1 (physicalSiteEquiv p (i, a)).2 =
      g.xConfig (configurationCoordinates p f) i a := by
  simp [fineXConfig]

@[simp] theorem fineZConfig_atSite (f : FineConfig p) (i : Fin 6 × Fin p) (a : Translation 3) :
    fineZConfig p g f (physicalSiteEquiv p (i, a)).1 (physicalSiteEquiv p (i, a)).2 =
      g.zConfig (configurationCoordinates p f) i a := by
  simp [fineZConfig]

theorem fineX_translation_covariant (b : Translation 3) (f : FineConfig p) :
    fineXConfig p g (Circuit.SUM.translateConfig (inclusion p b) f) =
      Circuit.SUM.translateConfig (inclusion p b) (fineXConfig p g f) := by
  funext i a
  obtain ⟨⟨j, n⟩, h⟩ := (physicalSiteEquiv p).surjective (i, a)
  have hi := congrArg Prod.fst h
  have ha := congrArg Prod.snd h
  change (physicalSiteEquiv p (j, n)).1 = i at hi
  change (physicalSiteEquiv p (j, n)).2 = a at ha
  rw [← hi, ← ha, fineXConfig_atSite]
  rw [configurationCoordinates_translation, g.x_translation_covariant]
  change g.xConfig (configurationCoordinates p f) j (n - b) = _
  rw [← fineXConfig_atSite p g f j (n - b), physicalSite_sub]
  rfl

theorem fineZ_translation_covariant (b : Translation 3) (f : FineConfig p) :
    fineZConfig p g (Circuit.SUM.translateConfig (inclusion p b) f) =
      Circuit.SUM.translateConfig (inclusion p b) (fineZConfig p g f) := by
  funext i a
  obtain ⟨⟨j, n⟩, h⟩ := (physicalSiteEquiv p).surjective (i, a)
  have hi := congrArg Prod.fst h
  have ha := congrArg Prod.snd h
  change (physicalSiteEquiv p (j, n)).1 = i at hi
  change (physicalSiteEquiv p (j, n)).2 = a at ha
  rw [← hi, ← ha, fineZConfig_atSite]
  rw [configurationCoordinates_translation, g.z_translation_covariant]
  change g.zConfig (configurationCoordinates p f) j (n - b) = _
  rw [← fineZConfig_atSite p g f j (n - b), physicalSite_sub]
  rfl

/-- Actual original-lattice displacement, including the residue-row offset. -/
theorem fine_displacement (a : Translation 3) :
    (physicalSiteEquiv p (g.destination a)).2 - (physicalSiteEquiv p (g.source a)).2 =
      inclusion p g.displacement + row p g.target.2 - row p g.control.2 := by
  change (inclusion p (a + g.displacement) + row p g.target.2) -
    (inclusion p a + row p g.control.2) = _
  rw [map_add]
  abel

theorem fine_distinct (a : Translation 3) :
    physicalSiteEquiv p (g.source a) ≠ physicalSiteEquiv p (g.destination a) := by
  simpa only [ne_eq, Equiv.apply_eq_iff_eq] using g.distinct_sites a

theorem fine_disjoint {a b : Translation 3} (h : a ≠ b) :
    physicalSiteEquiv p (g.source a) ≠ physicalSiteEquiv p (g.source b) ∧
    physicalSiteEquiv p (g.source a) ≠ physicalSiteEquiv p (g.destination b) ∧
    physicalSiteEquiv p (g.destination a) ≠ physicalSiteEquiv p (g.source b) ∧
    physicalSiteEquiv p (g.destination a) ≠ physicalSiteEquiv p (g.destination b) := by
  simpa only [ne_eq, Equiv.apply_eq_iff_eq] using g.disjoint_gates h

/-- Retained translations permute the original-site gate pairs. -/
theorem fine_translate_sites (a b : Translation 3) :
    physicalSiteEquiv p (g.source (a + b)) =
      (g.control.1, (physicalSiteEquiv p (g.source a)).2 + inclusion p b) ∧
    physicalSiteEquiv p (g.destination (a + b)) =
      (g.target.1, (physicalSiteEquiv p (g.destination a)).2 + inclusion p b) := by
  constructor
  · exact physicalSite_translate p _ _ a b
  · change physicalSiteEquiv p ((g.target.1, g.target.2), a + b + g.displacement) = _
    rw [show a + b + g.displacement = (a + g.displacement) + b by abel]
    exact physicalSite_translate p _ _ (a + g.displacement) b

variable (c : List (Circuit.SUM (ZMod p) 3 (Fin 6 × Fin p)))

def fineRangeBound : ℕ :=
  c.foldr (fun g t => max (Finset.univ.sup (fun i =>
    ((inclusion p g.displacement + row p g.target.2 - row p g.control.2) i).natAbs)) t) 0

theorem fine_distance_le_rangeBound (hg : g ∈ c) (a : Translation 3) (i : Fin 3) :
    (((physicalSiteEquiv p (g.destination a)).2 -
      (physicalSiteEquiv p (g.source a)).2) i).natAbs ≤ fineRangeBound p c := by
  rw [fine_displacement]
  induction c with
  | nil => simp at hg
  | cons h c ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact le_trans (Finset.le_sup (f := fun i =>
        ((inclusion p g.displacement + row p g.target.2 - row p g.control.2) i).natAbs)
        (Finset.mem_univ i)) (Nat.le_max_left _ _)
    · exact le_trans (ih hg) (Nat.le_max_right _ _)

/-- All geometric and both Pauli-action locality statements in original sites. -/
def FineLocality : Prop :=
  ∃ depth range : ℕ, depth = c.length ∧ ∀ g ∈ c,
    (∀ a, physicalSiteEquiv p (g.source a) ≠ physicalSiteEquiv p (g.destination a)) ∧
    (∀ a b, a ≠ b →
      physicalSiteEquiv p (g.source a) ≠ physicalSiteEquiv p (g.source b) ∧
      physicalSiteEquiv p (g.source a) ≠ physicalSiteEquiv p (g.destination b) ∧
      physicalSiteEquiv p (g.destination a) ≠ physicalSiteEquiv p (g.source b) ∧
      physicalSiteEquiv p (g.destination a) ≠ physicalSiteEquiv p (g.destination b)) ∧
    (∀ a i, (((physicalSiteEquiv p (g.destination a)).2 -
      (physicalSiteEquiv p (g.source a)).2) i).natAbs ≤ range) ∧
    (∀ b f, fineXConfig p g (Circuit.SUM.translateConfig (inclusion p b) f) =
      Circuit.SUM.translateConfig (inclusion p b) (fineXConfig p g f)) ∧
    (∀ b f, fineZConfig p g (Circuit.SUM.translateConfig (inclusion p b) f) =
      Circuit.SUM.translateConfig (inclusion p b) (fineZConfig p g f))

theorem fineLocality : FineLocality p c := by
  refine ⟨c.length, fineRangeBound p c, rfl, ?_⟩
  intro g hg
  exact ⟨fine_distinct p g, fun _ _ h => fine_disjoint p g h,
    fine_distance_le_rangeBound p g c hg, fineX_translation_covariant p g,
    fineZ_translation_covariant p g⟩

/-- A fully local no-ancilla circuit, on actual original-lattice sites,
transporting both literal stabilizer families to TC₁+TC₂ coarse checks. -/
theorem exists_noAncilla_fine_sumCircuit :
    ∃ c : List (Circuit.SUM (ZMod p) 3 (Fin 6 × Fin p)),
      PhysicalIsomorphism.Transports (c.map Circuit.Layer.sum) (Equiv.refl _)
        (expandMatrix p (Glued.xChecks (ZMod p)))
        (expandMatrix p (Glued.splitX (ZMod p)))
        (expandMatrix p (Glued.zGenerators (ZMod p)))
        (expandMatrix p (Glued.splitZ (ZMod p))) ∧
      Circuit.zAction c = quditMatrix p ∧
      Circuit.wordX (c.map Circuit.Layer.sum) = dagger (quditInverse p) ∧
      FineLocality p c := by
  obtain ⟨c, hc, hz, hx, _⟩ := exists_noAncilla_sumCircuit p
  exact ⟨c, hc, hz, hx, fineLocality p c⟩

end
end Decoupling.HighDim.GluedDirectional
