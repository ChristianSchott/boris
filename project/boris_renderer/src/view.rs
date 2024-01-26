use boris_shared::{BindingId, Def, DefEdgeKind, DefId, DefNode, DefSet, NodeKind, ThirBody};
use egui::{Context, Pos2, Rect, ScrollArea, Sense, Ui, Vec2};
use la_arena::Arena;

use crate::{body_drawer, DefLivelinessInfo, DrawBuffer, State, UsageKind};

struct Tree {
    assignments: Vec<DefId>,
    usages: Vec<(UsageKind, DefId)>,

    source_activity: DefSet,
    usage_activity: DefSet,

    binding: BindingId,
    mutable: bool,
    has_lt: bool,
}

impl Tree {
    fn new(defs: &Arena<Def>, binding: BindingId, mutable: bool, has_lt: bool) -> Self {
        Self {
            assignments: vec![],
            usages: vec![],
            source_activity: DefSet::new(defs),
            usage_activity: DefSet::new(defs),
            binding,
            mutable,
            has_lt,
        }
    }

    fn add_def(&mut self, kind: UsageKind, def: DefId) {
        if let Some((old_kind, _)) = self.usages.iter_mut().find(|(_, id)| *id == def) {
            if matches!(kind, UsageKind::Move(false)) {
                *old_kind = UsageKind::Move(false);
            }
        } else {
            self.usages.push((kind, def));
        }
    }

    fn merge(&mut self, other: &Tree) {
        for (kind, def) in other.usages.iter().copied() {
            self.add_def(kind, def);
        }
        for def in other.assignments.iter().copied() {
            if !self.assignments.contains(&def) {
                self.assignments.push(def);
            }
        }
        self.source_activity.or(&other.source_activity);
        self.usage_activity.or(&other.usage_activity);
    }

    fn add_usage(&mut self, kind: DefEdgeKind, def: DefId, activity: &DefSet) {
        let kind = match kind {
            DefEdgeKind::Move(partial) => UsageKind::Move(partial),
            DefEdgeKind::Copy => UsageKind::Copy,
            DefEdgeKind::Deref => UsageKind::Deref,
            DefEdgeKind::Ref(mutable) => UsageKind::Reference(mutable),
            DefEdgeKind::Reassign => {
                self.add_source(def, activity);
                return;
            }
            _ => {
                return;
            }
        };
        self.add_def(kind, def);
        self.usage_activity.or(activity)
    }

    fn add_source(&mut self, def: DefId, activity: &DefSet) {
        if !self.assignments.contains(&def) {
            self.assignments.push(def);
        }
        self.source_activity.or(activity);
    }

    fn activity(&self) -> DefSet {
        let mut activity = self.source_activity.clone();
        if self.has_lt {
            activity.and(&self.usage_activity);
        }
        activity
    }
}

pub fn boris_view(
    ctx: &Context,
    ui: &mut Ui,
    body: &ThirBody,
    selected_def: &mut Option<DefId>,
) -> Rect {
    let mut trees: Vec<Tree> = vec![];

    let mut insert_or_join = |tree: Tree| {
        if let Some(existing_tree) = trees.iter_mut().find(|existing| {
            existing.binding == tree.binding
                && existing
                    .usages
                    .iter()
                    .any(|(_, existing_def)| tree.usages.iter().any(|(_, def)| existing_def == def))
        }) {
            existing_tree.merge(&tree);
        } else {
            trees.push(tree);
        }
    };

    let add_tree = |def: DefId,
                    edges: &[(DefEdgeKind, DefId)],
                    active: &DefSet,
                    binding: BindingId,
                    mutable: bool,
                    has_lt: bool| {
        let mut tree = Tree::new(&body.defs, binding, mutable, has_lt);
        tree.add_source(def, active);
        for (kind, to) in edges {
            if let Some(DefNode { active, .. }) = body.def_graph.get(*to) {
                tree.add_usage(kind.clone(), *to, active);
            }
        }
        tree
    };

    let mut targets = vec![];
    let mut try_add_source_def = |def: DefId| {
        if let Some(DefNode {
            kind:
                NodeKind::Source {
                    binding,
                    mutable,
                    contains_lt,
                },
            edges,
            active,
        }) = body.def_graph.get(def)
        {
            // track references to their source (only one level currently..)
            if let Some(sources) = body.def_graph_inv.get(def) {
                for source in sources {
                    if let Some(origins) = body.def_graph_inv.get(*source) {
                        for origin in origins {
                            if let Some(DefNode {
                                kind:
                                    NodeKind::Source {
                                        binding,
                                        mutable,
                                        contains_lt,
                                    },
                                edges,
                                active,
                            }) = body.def_graph.get(*origin)
                            {
                                insert_or_join(add_tree(
                                    *origin,
                                    &edges,
                                    active,
                                    *binding,
                                    *mutable,
                                    *contains_lt,
                                ));
                            }
                        }
                    }
                }
            }

            targets.extend(edges.iter().map(|(_, to)| *to));

            let mut tree = add_tree(def, &edges, active, *binding, *mutable, *contains_lt);
            // if a source node has a direct connection to another source node, then it is a reassignment and we want to include it
            if let Some(sources) = body.def_graph_inv.get(def) {
                for source in sources {
                    if let Some(DefNode {
                        kind: NodeKind::Source { .. },
                        active,
                        edges,
                    }) = body.def_graph.get(*source)
                    {
                        tree.add_source(*source, active);
                        targets.extend(edges.iter().map(|(_, to)| *to));
                    }
                }
            }
            insert_or_join(tree);
            true
        } else {
            false
        }
    };

    if let Some(selected) = selected_def.clone() {
        if !try_add_source_def(selected) {
            // when clicking on a usage, find the corresponding source node
            if let Some(DefNode {
                kind: NodeKind::Usage,
                ..
            }) = body.def_graph.get(selected)
            {
                if let Some(sources) = body.def_graph_inv.get(selected) {
                    for source in sources.iter().cloned() {
                        try_add_source_def(source);
                    }
                }
            }
        }
    }

    // extend used references
    while let Some(top) = targets.pop() {
        match body.def_graph.get(top) {
            Some(DefNode { edges, .. }) => {
                for to in edges
                    .iter()
                    .filter_map(|(kind, to)| matches!(kind, DefEdgeKind::Lifetime).then_some(*to))
                {
                    // println!("track {top:?} to {to:?} ({:?})", body.def_graph.get(to));

                    match body.def_graph.get(to) {
                        Some(DefNode {
                            kind:
                                NodeKind::Source {
                                    binding,
                                    mutable,
                                    contains_lt,
                                },
                            edges,
                            active,
                        }) => {
                            targets.extend(edges.iter().filter_map(|(kind, to)| {
                                matches!(
                                    kind,
                                    DefEdgeKind::Copy
                                        | DefEdgeKind::Move(_)
                                        | DefEdgeKind::Ref(_)
                                        | DefEdgeKind::Deref
                                )
                                .then_some(*to)
                            }));
                            insert_or_join(add_tree(
                                to,
                                &edges,
                                active,
                                *binding,
                                *mutable,
                                *contains_lt,
                            ));
                        }
                        Some(DefNode {
                            kind: NodeKind::Usage,
                            ..
                        }) => {
                            // this can occur when assigning to a deref
                            if let Some(sources) = body.def_graph_inv.get(to) {
                                for source in sources {
                                    match body.def_graph.get(*source) {
                                        Some(DefNode {
                                            kind:
                                                NodeKind::Source {
                                                    binding,
                                                    mutable,
                                                    contains_lt,
                                                },
                                            edges,
                                            active,
                                        }) => {
                                            insert_or_join(add_tree(
                                                *source,
                                                &edges,
                                                active,
                                                *binding,
                                                *mutable,
                                                *contains_lt,
                                            ));
                                        }
                                        _ => (),
                                    }
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        }
    }

    let def_sets = Box::from_iter(trees.into_iter().map(|tree| {
        (
            tree.activity(),
            tree.assignments,
            tree.usages,
            tree.binding,
            tree.mutable,
        )
    }));
    let liveliness_info = DefLivelinessInfo::new(&body.defs, &def_sets);

    let state = State::new(
        selected_def.clone(),
        liveliness_info,
        body.never_defs.clone(),
        body.def_order.clone(),
        body.next_def_map.clone(),
    );
    let mut buffer = DrawBuffer::new(ctx); // TODO reuse & clear this instead of recreating
    let root_id = body_drawer::append_main_body(&mut buffer, body, state.clone());

    let mut draw = |ui: &mut Ui, size: Vec2| -> Rect {
        let (response, painter) = ui.allocate_painter(size, Sense::click());
        let pointer_pos = ctx.input(|input| input.pointer.hover_pos().unwrap_or(Pos2::ZERO));
        let selected = buffer.draw(
            &painter,
            response.rect,
            root_id,
            pointer_pos,
            &state,
            &body.conflicts,
            &body.selectable_defs,
        );

        ui.input(|input| {
            if let Some(selected_thir) = selected.selected_thir() {
                if input.pointer.button_clicked(egui::PointerButton::Primary) {
                    *selected_def = Some(selected_thir);
                }
            }
            if input.pointer.button_clicked(egui::PointerButton::Secondary) {
                *selected_def = None;
            }
        });
        response.rect
    };

    let available_size = ui.available_size();
    let size = buffer.size(root_id);
    let rect = if size.x > available_size.x || size.y > available_size.y {
        egui::ScrollArea::both()
            .drag_to_scroll(false)
            .show(ui, |ui| draw(ui, size))
            .inner
    } else {
        draw(ui, available_size)
    };
    Rect::from_min_size(rect.min, size)
}
