import formal_oet.vol_01.ch_05_operator_networks.transition_trajectories

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
variable {X V : Type} {bot : X}

namespace OperatorTransitionGraph
variable (T : OperatorTransitionGraph X bot V)

/-- OET anchor: h-86752cb60c8e01e3
The textbook's disjoint outgoing transition domains, stated on the raw graph. -/
def HasDisjointOutgoingDomains : Prop :=
  ∀ v w w' : V, w ≠ w' → Disjoint (T.edge_domain v w) (T.edge_domain v w')

/-- OET anchor: h-86752cb60c8e01e3
The entry pieces partition the source domain and lie in their node domains.
Empty pieces encode non-entry nodes; the entry-node set is exactly the nodes
with nonempty pieces, so no nonempty-node assumption excludes the empty network. -/
structure EntryPartition (U : Set X) (entrance : V → Set X) : Prop where
  subset_node_dom : ∀ v, entrance v ⊆ T.node_dom v
  cover : (⋃ v, entrance v) = U
  disjoint : ∀ v w, v ≠ w → Disjoint (entrance v) (entrance w)

/-- Choose an outgoing edge when one exists, and stop otherwise. -/
noncomputable def choice_of_edges (v : V) (y : X) : OutputChoice V := by
  classical
  exact if h : ∃ w, y ∈ T.edge_domain v w then .next h.choose else .stop

theorem choice_of_edges_next_iff (hdet : T.HasDisjointOutgoingDomains)
    {v w : V} {y : X} :
    T.choice_of_edges v y = .next w ↔ y ∈ T.edge_domain v w := by
  classical
  unfold choice_of_edges
  split_ifs with h
  · constructor
    · intro heq
      have hw := OutputChoice.next.inj heq
      simpa [hw] using h.choose_spec
    · intro hy
      have hw : h.choose = w := by
        by_contra hn
        exact Set.disjoint_left.mp (hdet v h.choose w hn) h.choose_spec hy
      simp [hw]
  · simp only [false_iff]
    exact fun hy => h ⟨w, hy⟩

theorem choice_of_edges_stop_iff {v : V} {y : X} :
    T.choice_of_edges v y = .stop ↔ ¬ ∃ w, y ∈ T.edge_domain v w := by
  classical
  unfold choice_of_edges
  split_ifs <;> simp_all

theorem terminal_trajectory_to_chosen_path (hdet : T.HasDisjointOutgoingDomains)
    {v x states} (h : T.TerminalTrajectoryFrom v x states) :
    TerminalPathFrom T.node_op T.choice_of_edges v x (states.map Prod.fst) := by
  induction h with
  | stop hx ht =>
    apply TerminalPathFrom.stop
    apply T.choice_of_edges_stop_iff.mpr
    rintro ⟨w, hw⟩
    exact ht.2 (Set.mem_iUnion.mpr ⟨w, hw⟩)
  | next step tail ih =>
    rw [step.2.1] at ih
    exact .next ((T.choice_of_edges_next_iff hdet).mpr (step.2.1 ▸ step.2.2)) ih

/-- Disjoint raw edge domains force uniqueness of the full labelled state
trajectory, before any operational finite network has been constructed. -/
theorem terminal_trajectory_unique_of_disjoint (hdet : T.HasDisjointOutgoingDomains)
    {v x states states'} (h : T.TerminalTrajectoryFrom v x states)
    (h' : T.TerminalTrajectoryFrom v x states') : states = states' := by
  have hp := terminal_path_unique (T.terminal_trajectory_to_chosen_path hdet h)
    (T.terminal_trajectory_to_chosen_path hdet h')
  rw [T.finite_trajectory_eq_state_trace (T.terminal_trajectory_finite h),
    T.finite_trajectory_eq_state_trace (T.terminal_trajectory_finite h'), hp]

namespace EntryPartition
variable {T} {U : Set X} {entrance : V → Set X}
variable (hpart : T.EntryPartition U entrance)
include hpart

theorem mem_unique_entry {x : X} (hx : x ∈ U) : ∃! v, x ∈ entrance v := by
  have hmem : x ∈ ⋃ v, entrance v := hpart.cover ▸ hx
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmem
  refine ⟨v, hv, ?_⟩
  intro w hw
  by_contra hn
  exact Set.disjoint_left.mp (hpart.disjoint w v hn) hw hv

noncomputable def entry (x : {x // x ∈ U}) : V :=
  (hpart.mem_unique_entry x.property).exists.choose

theorem entry_mem (x : {x // x ∈ U}) : x.val ∈ entrance (hpart.entry x) :=
  (hpart.mem_unique_entry x.property).exists.choose_spec

theorem entry_eq_iff (x : {x // x ∈ U}) (v : V) :
    hpart.entry x = v ↔ x.val ∈ entrance v := by
  constructor
  · intro heq
    simpa [heq] using hpart.entry_mem x
  · intro hv
    exact ((hpart.mem_unique_entry x.property).unique hv (hpart.entry_mem x)).symm

theorem piece_subset_source (v : V) : entrance v ⊆ U := by
  intro x hx
  rw [← hpart.cover]
  exact Set.mem_iUnion.mpr ⟨v, hx⟩

theorem bot_not_mem : bot ∉ U := by
  intro hx
  have hdom := hpart.subset_node_dom _ (hpart.entry_mem ⟨bot, hx⟩)
  exact hdom (T.node_op _).preserves_bot

end EntryPartition

variable {U : Set X} {entrance : V → Set X}

/-- OET anchor: h-86752cb60c8e01e3
Import the textbook's four raw-data conditions into the operational encoding.
The assumptions supply only graph terminal trajectories, their uniform bound,
and node occurrence; routing, entry choice and terminal paths are constructed.
No operational network or desired roundtrip conclusion is assumed. -/
noncomputable def to_finite_network (hpart : T.EntryPartition U entrance)
    (hdet : T.HasDisjointOutgoingDomains) (bound : Nat)
    (hterm : ∀ x v, x ∈ entrance v → ∃ states,
      T.TerminalTrajectoryFrom v x states ∧ states.length ≤ bound)
    (hreach : ∀ v, ∃ x w states, x ∈ entrance w ∧
      T.TerminalTrajectoryFrom w x states ∧ v ∈ states.map Prod.fst) :
    FiniteOperatorNetwork X bot V where
  U := U
  bot_not_mem := hpart.bot_not_mem
  node_fintype := T.node_fintype
  node_op := T.node_op
  node_dom_nonempty := T.node_dom_nonempty
  entry := hpart.entry
  entry_mem := fun x => hpart.subset_node_dom _ (hpart.entry_mem x)
  choice := T.choice_of_edges
  choice_next_mem := by
    intro v w y _ hc
    exact T.edge_domain_subset_node_dom v w ((T.choice_of_edges_next_iff hdet).mp hc)
  depth_bound := bound
  path_of := fun x => (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose.map Prod.fst
  path_terminal := fun x => T.terminal_trajectory_to_chosen_path hdet
    (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.1
  path_length_le_depth := by
    intro x
    simpa only [List.length_map] using
      (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.2
  node_reachable := by
    intro v
    obtain ⟨x, w, states, hx, ht, hv⟩ := hreach v
    let input : {x // x ∈ U} := ⟨x, hpart.piece_subset_source w hx⟩
    have he : hpart.entry input = w := (hpart.entry_eq_iff input w).mpr hx
    refine ⟨input, ?_⟩
    have ht' : T.TerminalTrajectoryFrom (hpart.entry input) x states := he ▸ ht
    have hs := T.terminal_trajectory_unique_of_disjoint hdet ht'
      (hterm input.val (hpart.entry input) (hpart.entry_mem input)).choose_spec.1
    simpa only [hs] using hv

variable (hpart : T.EntryPartition U entrance) (hdet : T.HasDisjointOutgoingDomains)
  (bound : Nat)
  (hterm : ∀ x v, x ∈ entrance v → ∃ states,
    T.TerminalTrajectoryFrom v x states ∧ states.length ≤ bound)
  (hreach : ∀ v, ∃ x w states, x ∈ entrance w ∧
    T.TerminalTrajectoryFrom w x states ∧ v ∈ states.map Prod.fst)

@[simp] theorem to_finite_network_source :
    (T.to_finite_network hpart hdet bound hterm hreach).U = U := rfl

@[simp] theorem to_finite_network_node_op :
    (T.to_finite_network hpart hdet bound hterm hreach).node_op = T.node_op := rfl

/-- Every entry piece, including empty ones, is preserved exactly. -/
@[simp] theorem to_finite_network_entry_domain (v : V) :
    (T.to_finite_network hpart hdet bound hterm hreach).entry_domain v = entrance v := by
  ext x
  constructor
  · rintro ⟨hx, he⟩
    exact (hpart.entry_eq_iff ⟨x, hx⟩ v).mp he
  · intro hx
    exact ⟨hpart.piece_subset_source v hx,
      (hpart.entry_eq_iff ⟨x, hpart.piece_subset_source v hx⟩ v).mpr hx⟩

/-- Raw edge domains are retained even away from all entrance trajectories. -/
@[simp] theorem to_finite_network_edge_domain (v w : V) :
    (T.to_finite_network hpart hdet bound hterm hreach).edge_domain v w =
      T.edge_domain v w := by
  ext y
  change (y ∈ (T.node_op v).func '' dom (T.node_op v) ∧
    T.choice_of_edges v y = .next w) ↔ y ∈ T.edge_domain v w
  rw [T.choice_of_edges_next_iff hdet]
  exact ⟨And.right, fun hy => ⟨T.edge_domain_subset_node_image v w hy, hy⟩⟩

/-- OET anchor: h-86752cb60c8e01e3
The import followed by forgetting is exactly the original transition graph,
including local operators and unused transition domains. -/
@[simp] theorem to_finite_network_transition_graph :
    (T.to_finite_network hpart hdet bound hterm hreach).to_transition_graph = T := by
  have hedges :
      (T.to_finite_network hpart hdet bound hterm hreach).to_transition_graph.edge_domain =
        T.edge_domain := by
    funext v w
    exact T.to_finite_network_edge_domain hpart hdet bound hterm hreach v w
  cases T
  simp only [FiniteOperatorNetwork.to_transition_graph, to_finite_network] at hedges ⊢
  congr 1

/-- Each supplied terminal trajectory becomes the stored complete node list;
thus the arbitrary choice of termination witnesses does not alter paths. -/
theorem to_finite_network_path_of (x : {x // x ∈ U}) {states}
    (ht : T.TerminalTrajectoryFrom (hpart.entry x) x.val states) :
    (T.to_finite_network hpart hdet bound hterm hreach).path_of x =
      states.map Prod.fst := by
  change (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose.map Prod.fst = _
  rw [T.terminal_trajectory_unique_of_disjoint hdet
    (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.1 ht]

end OperatorTransitionGraph
end formal_oet.vol_01.ch_05_operator_networks
