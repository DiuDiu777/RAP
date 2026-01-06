use super::graph::*;
use rustc_middle::mir::SourceInfo;
use std::usize;

#[derive(Debug, Copy, Clone)]
pub struct LocalSpot {
    pub bb: Option<usize>,
    pub local: Option<usize>,
}

impl LocalSpot {
    pub fn new(bb: usize, local: usize) -> Self {
        LocalSpot {
            bb: Some(bb),
            local: Some(local),
        }
    }
    pub fn from_local(local: usize) -> Self {
        LocalSpot {
            bb: None,
            local: Some(local),
        }
    }
    pub fn default() -> Self {
        LocalSpot {
            bb: None,
            local: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DropRecord {
    pub value_index: usize,
    pub is_dropped: bool,
    pub drop_spot: LocalSpot,
    pub prop_chain: Vec<usize>,
    pub has_dropped_field: bool,
}

impl DropRecord {
    pub fn new(value_index: usize, is_dropped: bool, drop_spot: LocalSpot) -> Self {
        DropRecord {
            value_index,
            is_dropped,
            drop_spot,
            prop_chain: Vec::new(),
            has_dropped_field: false,
        }
    }
    pub fn false_record(value_index: usize) -> Self {
        DropRecord {
            value_index,
            is_dropped: false,
            drop_spot: LocalSpot::default(),
            prop_chain: Vec::new(),
            has_dropped_field: false,
        }
    }
    pub fn from(value_index: usize, record: &DropRecord) -> Self {
        DropRecord {
            value_index,
            is_dropped: record.is_dropped,
            drop_spot: record.drop_spot.clone(),
            prop_chain: record.prop_chain.clone(),
            has_dropped_field: record.has_dropped_field,
        }
    }
}

impl<'tcx> SafeDropGraph<'tcx> {
    /*
     * Mark the node as dropped.
     * flag_cleanup: used to distinguish if a bug occurs in the unwinding path.
     */
    pub fn add_to_drop_record(
        &mut self,
        value_idx: usize, // the value to be dropped
        bb_idx: usize,    // the block via_idx is dropped
        _info: &SourceInfo,
        flag_cleanup: bool,
    ) {
        //Rc drop
        if self.mop_graph.values[value_idx].is_corner_case() {
            return;
        }
        if self.df_check(value_idx, bb_idx, self.mop_graph.span, flag_cleanup) {
            return;
        }
        if !self.drop_record[value_idx].is_dropped {
            let drop_spot = LocalSpot::new(bb_idx, self.mop_graph.values[value_idx].local);
            self.drop_record[value_idx] = DropRecord::new(value_idx, true, drop_spot);
            rap_debug!(
                "add_to_drop_record: idx = {}, {:?}",
                value_idx,
                self.drop_record[value_idx]
            );

            self.update_drop_bottom_up(value_idx);
            self.update_drop_top_down(value_idx, drop_spot);
        }
    }

    pub fn update_drop_alias(&mut self, idx: usize, drop_spot: LocalSpot) {
        if let Some(aliases) = self.mop_graph.get_alias_set(idx) {
            for i in aliases {
                if i != idx {
                    self.drop_record[i] = DropRecord::new(i, true, drop_spot);
                    rap_debug!("update_drop_alias: i = {}, {:?}", i, self.drop_record[i]);
                }
            }
        }
    }

    ///drop the fields of the root node.
    pub fn update_drop_top_down(&mut self, value_idx: usize, drop_spot: LocalSpot) {
        for (_field_id, field_value_id) in self.mop_graph.values[value_idx].fields.clone() {
            if self.mop_graph.values[value_idx].is_tuple()
                && !self.mop_graph.values[field_value_id].need_drop
            {
                continue;
            }
            self.drop_record[field_value_id] = DropRecord::new(value_idx, true, drop_spot);
            rap_debug!(
                "update_drop_top_down: field_value_id = {}, {:?}",
                field_value_id,
                self.drop_record[field_value_id]
            );
        }
    }

    pub fn update_drop_bottom_up(&mut self, value_idx: usize) {
        // sync the father node: has_dropped_field
        let mut father = self.mop_graph.values[value_idx].father.clone();
        let _prop_chain = vec![value_idx];
        while let Some(father_info) = father {
            let father_idx = father_info.father_value_id;
            self.drop_record[father_idx].has_dropped_field = true;
            self.drop_record[father_idx].prop_chain.push(father_idx);
            father = self.mop_graph.values[father_idx].father.clone();
        }
    }

    pub fn sync_drop_from_alias(&mut self, idx: usize) {
        if idx >= self.mop_graph.values.len() {
            return;
        }
        let local = self.mop_graph.values[idx].local;
        if self.drop_record[local].is_dropped {
            self.drop_record[idx] = self.drop_record[local].clone();
        }
        if let Some(aliases) = self.mop_graph.get_alias_set(local) {
            for value_idx in aliases {
                // set idx as dropped if any of its alias has been dropped.
                if self.drop_record[value_idx].is_dropped {
                    self.drop_record[idx] = self.drop_record[value_idx].clone();
                }
            }
        }
    }
}
