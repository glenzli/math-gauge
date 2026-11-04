import formal_oet.vol_01.ch_05_operator_networks.network_presentation
import formal_oet.vol_01.ch_05_operator_networks.network_routing

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open FiniteOperatorNetwork
noncomputable section
variable {X V : Type} {bot : X}

/-- The finite partition and local operators in the node-domain refinement definition. -/
structure NodePartitionData (N : FiniteOperatorNetwork X bot V) (target : V) where
  count : ℕ
  count_pos : 0 < count
  piece : Fin count → Set X
  nonempty : ∀ a, (piece a).Nonempty
  disjoint : ∀ {a b}, a ≠ b → Disjoint (piece a) (piece b)
  cover : (⋃ a, piece a) = N.node_dom target
  local_op : Fin count → Operator X bot
  local_domain : ∀ a, dom (local_op a) = piece a
  local_eq : ∀ a x, x ∈ piece a → (local_op a).func x = (N.node_op target).func x

namespace NodePartitionData
variable {N : FiniteOperatorNetwork X bot V} {target : V}
variable (P : NodePartitionData N target)

/--
OET anchor: h-eddd1f2d0a9d3528
The prescribed domain and local equality determine the whole subnode operator.
-/
theorem local_op_eq_restrict (a : Fin P.count) :
    P.local_op a = restrict_operator (N.node_op target) (P.piece a) := by
  apply Operator.ext
  funext x
  by_cases hx : x ∈ P.piece a
  · rw [restrict_operator_apply_of_mem _ _ hx]
    exact P.local_eq a x hx
  · rw [restrict_operator_apply_of_not_mem _ _ hx]
    by_contra hne
    exact hx ((P.local_domain a) ▸ hne)

abbrev Label := {v : V // v ≠ target} ⊕ Fin P.count

/-- On the target domain the unique partition member is chosen. Outside it the
choice is an irrelevant totalization used only to define the routing function. -/
def piece_at (x : X) : Fin P.count := by
  classical
  exact if h : ∃ a, x ∈ P.piece a then h.choose else ⟨0, P.count_pos⟩

theorem mem_piece_at (x : X) (hx : x ∈ N.node_dom target) : x ∈ P.piece (P.piece_at x) := by
  classical
  have h : ∃ a, x ∈ P.piece a := by rw [← P.cover] at hx; exact Set.mem_iUnion.mp hx
  simpa [piece_at, h] using h.choose_spec

theorem piece_at_unique (x : X) (a : Fin P.count) (hx : x ∈ P.piece a) : P.piece_at x = a := by
  have hxdom : x ∈ N.node_dom target := by rw [← P.cover]; exact Set.mem_iUnion.mpr ⟨a, hx⟩
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint h) (P.mem_piece_at x hxdom) hx

def projection : P.Label → V
  | .inl v => v.val
  | .inr _ => target

def lift_label (v : V) (x : X) : P.Label := by
  classical
  exact if hv : v = target then .inr (P.piece_at x) else .inl ⟨v, hv⟩

@[simp] theorem projection_lift (v : V) (x : X) : P.projection (P.lift_label v x) = v := by
  classical
  by_cases hv : v = target <;> simp [lift_label, projection, hv]

def node_op : P.Label → Operator X bot
  | .inl v => N.node_op v.val
  | .inr a => P.local_op a

theorem lift_mem_dom (v : V) (x : X) (hx : x ∈ N.node_dom v) :
    x ∈ dom (P.node_op (P.lift_label v x)) := by
  classical
  by_cases hv : v = target
  · subst v
    simp only [lift_label, ↓reduceDIte, node_op, P.local_domain]
    exact P.mem_piece_at x hx
  · simpa [lift_label, hv, node_op] using hx

theorem lift_apply (v : V) (x : X) (hx : x ∈ N.node_dom v) :
    (P.node_op (P.lift_label v x)).func x = (N.node_op v).func x := by
  classical
  by_cases hv : v = target
  · subst v
    simp only [lift_label, ↓reduceDIte, node_op]
    exact P.local_eq _ x (P.mem_piece_at x hx)
  · simp [lift_label, hv, node_op]

theorem node_domain_subset_original (v : P.Label) :
    dom (P.node_op v) ⊆ N.node_dom (P.projection v) := by
  cases v with
  | inl v => exact Set.Subset.rfl
  | inr a =>
    intro x hx
    rw [node_op, P.local_domain a] at hx
    change x ∈ N.node_dom target
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨a, hx⟩

theorem node_apply_eq_original (v : P.Label) (x : X) (hx : x ∈ dom (P.node_op v)) :
    (P.node_op v).func x = (N.node_op (P.projection v)).func x := by
  cases v with
  | inl v => rfl
  | inr a => exact P.local_eq a x ((P.local_domain a) ▸ hx)

def choice (v : P.Label) (z : X) : OutputChoice P.Label :=
  map_output_choice (fun w => P.lift_label w z) (N.choice (P.projection v) z)

/--
OET anchor: h-eddd1f2d0a9d3528
A split self-loop must select both the source piece and the destination piece.
This is the routing part of the double-intersection edge formula.
-/
theorem self_loop_choice_iff (a b : Fin P.count) (z : X)
    (hz : z ∈ (P.local_op a).func '' P.piece a) :
    P.choice (.inr a) z = .next (.inr b) ↔
      z ∈ N.edge_domain target target ∧ z ∈ P.piece b := by
  classical
  have himage : z ∈ N.node_image target := by
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, (P.local_eq a x hx).symm⟩
    change x ∈ N.node_dom target
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨a, hx⟩
  constructor
  · intro h
    unfold choice map_output_choice at h
    split at h
    · contradiction
    · rename_i v hv
      have hlift : P.lift_label v z = .inr b := OutputChoice.next.inj h
      have hvtarget : v = target := by
        have hproj := congrArg P.projection hlift
        change P.projection (P.lift_label v z) = target at hproj
        rw [P.projection_lift] at hproj
        exact hproj
      subst v
      have hpiece : P.piece_at z = b := by
        simpa [lift_label] using hlift
      have hedge : z ∈ N.edge_domain target target := ⟨himage, hv⟩
      refine ⟨hedge, ?_⟩
      rw [← hpiece]
      exact P.mem_piece_at z (N.edge_domain_subset_node_dom hedge)
  · rintro ⟨hedge, hpiece⟩
    have hchoice : N.choice target z = .next target := hedge.2
    simp [choice, projection, map_output_choice, hchoice, lift_label,
      P.piece_at_unique z b hpiece]

theorem choice_next_mem {v w : P.Label} {x : X}
    (hx : x ∈ dom (P.node_op v)) (hc : P.choice v ((P.node_op v).func x) = .next w) :
    (P.node_op v).func x ∈ dom (P.node_op w) := by
  unfold choice map_output_choice at hc
  split at hc
  · contradiction
  · rename_i u hu
    cases hc
    apply P.lift_mem_dom
    have hdom := P.node_domain_subset_original v hx
    rw [P.node_apply_eq_original v x hx] at hu ⊢
    exact N.choice_next_mem hdom hu

/-- Recolour each target occurrence using its actual current input. -/
def colour_path (P : NodePartitionData N target) : List V → X → List P.Label
  | [], _ => []
  | v :: rest, x => P.lift_label v x :: P.colour_path rest ((N.node_op v).func x)

@[simp] theorem colour_path_length (p : List V) (x : X) :
    (P.colour_path p x).length = p.length := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => simp [colour_path, ih]

@[simp] theorem colour_path_projection (p : List V) (x : X) :
    (P.colour_path p x).map P.projection = p := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => simp [colour_path, ih]

theorem coloured_terminal {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) (hx : x ∈ N.node_dom v) :
    TerminalPathFrom P.node_op P.choice (P.lift_label v x) x (P.colour_path p x) := by
  induction ht with
  | @stop v x hs =>
    apply TerminalPathFrom.stop
    simp [choice, P.lift_apply v x hx, hs, map_output_choice]
  | @next v w x rest hs ht ih =>
    apply TerminalPathFrom.next (γ := P.lift_label w ((N.node_op v).func x))
    · simp [choice, P.lift_apply v x hx, hs, map_output_choice]
    · rw [P.lift_apply v x hx]
      exact ih (N.choice_next_mem hx hs)

theorem coloured_eval {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) (hx : x ∈ N.node_dom v) :
    chain_eval_nodes_core P.node_op (P.colour_path p x) x =
      chain_eval_nodes_core N.node_op p x := by
  induction ht with
  | @stop v x hs => simp [colour_path, chain_eval_nodes_core, P.lift_apply v x hx]
  | @next v w x rest hs ht ih =>
    simp only [colour_path, chain_eval_nodes_core, P.lift_apply v x hx]
    exact ih (N.choice_next_mem hx hs)

/-- Every finite-network obligation is derived before unreachable-piece deletion. -/
def presentation : FiniteNetworkPresentation X bot P.Label := by
  classical
  letI := N.node_fintype
  exact {
    U := N.U
    bot_not_mem := N.bot_not_mem
    node_fintype := inferInstance
    node_op := P.node_op
    node_dom_nonempty := by
      intro v
      cases v with
      | inl v => exact N.node_dom_nonempty v.val
      | inr a => simpa only [node_op, P.local_domain] using P.nonempty a
    entry := fun x => P.lift_label (N.entry x) x.val
    entry_mem := fun x => P.lift_mem_dom (N.entry x) x.val (N.entry_mem x)
    choice := P.choice
    choice_next_mem := P.choice_next_mem
    depth_bound := N.depth_bound
    path_of := fun x => P.colour_path (N.path_of x) x.val
    path_terminal := fun x => P.coloured_terminal (N.path_terminal x) (N.entry_mem x)
    path_length_le_depth := by intro x; simpa using N.path_length_le_depth x
  }

/--
OET anchor: h-eddd1f2d0a9d3528
Actual node-domain refinement, including deletion of all unreachable pieces.
-/
def network := P.presentation.prune

/--
OET anchor: h-012f4ba72aeb3f20
The constructed refinement has exactly the recoloured original paths.
-/
theorem network_path_labels (x : N.U) :
    (P.network.path_of x).map Subtype.val = P.colour_path (N.path_of x) x.val :=
  P.presentation.prune_path_labels x

/--
OET anchor: h-012f4ba72aeb3f20
Forgetting split labels recovers the actual original path, so its length is unchanged.
-/
theorem network_path_projection (x : N.U) :
    (P.network.path_of x).map (fun v => P.projection v.val) = N.path_of x := by
  change List.map (P.projection ∘ Subtype.val) (P.network.path_of x) = _
  rw [← List.map_map, P.network_path_labels, P.colour_path_projection]

/--
OET anchor: h-012f4ba72aeb3f20
The actual constructed and pruned domain refinement has the same global operator.
-/
theorem network_extensional_eq : P.network.extensional_operator = N.extensional_operator := by
  classical
  apply Operator.ext
  funext x
  by_cases hx : x ∈ N.U
  · change (if h : x ∈ N.U then P.network.eval ⟨x, h⟩ else bot) = _
    rw [dif_pos hx]
    change P.presentation.prune.eval ⟨x, hx⟩ = _
    rw [FiniteNetworkPresentation.prune_eval]
    exact (P.coloured_eval (N.path_terminal ⟨x, hx⟩) (N.entry_mem _)).trans
      (N.extensional_apply_eq_chain_eval_path ⟨x, hx⟩).symm
  · simp [extensional_operator, network, presentation, FiniteNetworkPresentation.prune, hx]

end NodePartitionData
end
end formal_oet.vol_01.ch_05_operator_networks
