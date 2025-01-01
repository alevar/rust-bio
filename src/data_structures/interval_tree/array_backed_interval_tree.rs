use num_traits::Bounded;

use crate::utils::Interval;
use std::cmp::min;
use std::iter::FromIterator;

/// A `find` query on the interval tree does not directly return references to the intervals in the
/// tree but wraps the fields `interval` and `data` in an `Entry`.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
struct InternalEntry<E: EntryT> {
    data: E,
    max: E::N,
    index: usize, // the position of the entry when it was first inserted
}

impl<E> InternalEntry<E>
where
    E: EntryT,
{
    fn interval(&self) -> &Interval<E::N> {
        self.data.interval()
    }
}

pub trait EntryT {
    type N: Ord + Clone + Copy + std::fmt::Debug;

    fn interval(&self) -> &Interval<Self::N>;
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ArrayBackedIntervalTree<E>
where
    E: EntryT,
{
    entries: Vec<InternalEntry<E>>,
    index: Vec<usize>, // holds mappings from the index of the original entry to the index in the tree. used for retrieval
    max_level: usize,
    indexed: bool,
}

impl<E> Default for ArrayBackedIntervalTree<E>
where
    E: EntryT,
    E::N: Default,
{
    fn default() -> Self {
        ArrayBackedIntervalTree {
            entries: Vec::new(),
            index: Vec::new(),
            max_level: 0,
            indexed: false,
        }
    }
}

impl<E> ArrayBackedIntervalTree<E>
where
    E: EntryT,
    E::N: Default,
{
    pub fn new() -> Self {
        Default::default()
    }

    pub fn insert(&mut self, entry: E) {
        let max = entry.interval().end;
        self.entries.push(InternalEntry {
            data: entry,
            max,
            index: self.entries.len(),
        });
        self.index.push(self.entries.len()-1);
        self.indexed = false;
    }

    pub fn index(&mut self) {
        if !self.indexed {
            self.entries.sort_by_key(|e| e.interval().start);
            // construct index by pulling index from entries after sort
            self.index = self.entries.iter().map(|e| e.index).collect();
            self.index_core();
            self.indexed = true;
        }
    }

    fn index_core(&mut self) {
        let a = &mut self.entries;
        if a.is_empty() {
            return;
        }

        let n = a.len();
        let mut last_i = 0;
        let mut last_value = a[0].max;
        (0..n).step_by(2).for_each(|i| {
            last_i = i;
            a[i].max = a[i].interval().end;
            last_value = a[i].max;
        });
        let mut k = 1;
        while (1 << k) <= n {
            // process internal nodes in the bottom-up order
            let x = 1 << (k - 1);
            let i0 = (x << 1) - 1; // i0 is the first node
            let step = x << 2;
            for i in (i0..n).step_by(step) {
                // traverse all nodes at level k
                let end_left = a[i - x].max; // max value of the left child
                let end_right = if i + x < n { a[i + x].max } else { last_value }; // max value of the right child
                let end = max3(a[i].interval().end, end_left, end_right);
                a[i].max = end;
            }
            last_i = if (last_i >> k & 1) > 0 {
                last_i - x
            } else {
                last_i + x
            };
            if last_i < n && a[last_i].max > last_value {
                last_value = a[last_i].max
            }
            k += 1;
        }
        self.max_level = k - 1;
    }

    /// Get the entry at the given index
    /// Returns `None` if the index is out of bounds
    /// 
    /// # Arguments
    /// 
    /// * `index` - The index of the entry to get
    /// 
    /// # Example
    /// 
    /// ```
    /// use bio::data_structures::interval_tree::ArrayBackedIntervalTree;
    /// 
    /// let mut tree = ArrayBackedIntervalTree::new();
    /// tree.insert(12..34, 0);
    /// tree.insert(0..23, 1);
    /// tree.insert(34..56, 2);
    /// tree.index()
    /// 
    /// assert_eq!(tree.get(0), Some(&0));
    /// assert_eq!(tree.get(1), Some(&1));
    /// assert_eq!(tree.get(2), Some(&2));
    pub fn get(&self, index: usize) -> Option<&E> {
        let tmp = self.index.get(index);
        tmp.map(|&i| &self.entries[i].data)
    }

    /// Find overlapping intervals in the index.
    /// Returns a vector of entries, consisting of the interval and its associated data.
    ///
    /// # Arguments
    ///
    /// * `interval` - The interval for which overlaps are to be found in the index. Can also be a `Range`.
    ///
    /// # Panics
    ///
    /// Panics if this `IITree` instance has not been indexed yet.
    pub fn find<I>(&self, interval: I) -> Vec<&E>
    where
        I: Into<Interval<E::N>>,
    {
        let mut buf = Vec::with_capacity(512);
        self.find_into(interval, &mut buf);
        buf
    }

    /// Find overlapping intervals in the index
    ///
    /// # Arguments
    ///
    /// * `interval` - The interval for which overlaps are to be found in the index. Can also be a `Range`.
    /// * `results` - A reusable buffer vector for storing the results.
    ///
    /// # Panics
    ///
    /// Panics if this `IITree` instance has not been indexed yet.
    pub fn find_into<'b, 'a: 'b, I>(
        &'a self,
        interval: I,
        results: &'b mut Vec<&'a E>,
    ) 
    where
        I: Into<Interval<E::N>>,
    {
        if !self.indexed {
            panic!("This IITree has not been indexed yet. Call `index()` first.")
        }

        let interval = interval.into();
        let (start, end) = (interval.start, interval.end);
        let n = self.entries.len() as usize;
        let a = &self.entries;
        results.clear();
        let mut stack = [StackCell::empty(); 64];
        // push the root; this is a top down traversal
        stack[0].k = self.max_level;
        stack[0].x = (1 << self.max_level) - 1;
        stack[0].w = false;
        let mut t = 1;
        while t > 0 {
            t -= 1;
            let StackCell { k, x, w } = stack[t];
            if k <= 3 {
                // we are in a small subtree; traverse every node in this subtree
                let i0 = x >> k << k;
                let i1 = min(i0 + (1 << (k + 1)) - 1, n);
                for (i, node) in a.iter().enumerate().take(i1).skip(i0) {
                    if node.interval().start >= end {
                        break;
                    }
                    if start < node.interval().end {
                        // if overlap, append to `results`
                        results.push(&self.entries[i].data);
                    }
                }
            } else if !w {
                // if left child not processed
                let y = x - (1 << (k - 1)); // the left child of x; NB: y may be out of range (i.e. y>=n)
                stack[t].k = k;
                stack[t].x = x;
                stack[t].w = true; // re-add node x, but mark the left child having been processed
                t += 1;
                if y >= n || a[y].max > start {
                    // push the left child if y is out of range or may overlap with the query
                    stack[t].k = k - 1;
                    stack[t].x = y;
                    stack[t].w = false;
                    t += 1;
                }
            } else if x < n && a[x].interval().start < end {
                // need to push the right child
                if start < a[x].interval().end {
                    results.push(&self.entries[x].data);
                }
                stack[t].k = k - 1;
                stack[t].x = x + (1 << (k - 1));
                stack[t].w = false;
                t += 1;
            }
        }
    }

    /// Returns the first entry in the tree
    pub fn first<'a>(&'a self) -> Option<&'a E> {
        match self.entries.first() {
            Some(entry) => Some(&entry.data),
            None => None,
        }
    }
    pub fn first_mut<'a>(&'a mut self) -> Option<&'a mut E> {
        match self.entries.first_mut() {
            Some(entry) => Some(&mut entry.data),
            None => None,
            
        }
    }
    /// Returns the last entry in the tree
    pub fn last<'a>(&'a self) -> Option<&'a E> {
        match self.entries.last() {
            Some(entry) => Some(&entry.data),
            None => None,
        }
    }
    pub fn last_mut<'a>(&'a mut self) -> Option<&'a mut E> {
        match self.entries.last_mut() {
            Some(entry) => Some(&mut entry.data),
            None => None,
        }
    }

    /// Returns the number of entries in the tree
    /// 
    /// # Example
    /// 
    /// ```
    /// use bio::data_structures::interval_tree::ArrayBackedIntervalTree;
    /// 
    /// let mut tree = ArrayBackedIntervalTree::new();
    /// tree.insert(12..34, 0);
    /// tree.insert(0..23, 1);
    /// tree.insert(34..56, 2);
    /// 
    /// assert_eq!(tree.len(), 3);
    /// ```
    pub fn len<'a>(&'a self) -> usize {
        self.entries.len()
    }
}

impl<E> FromIterator<E> for ArrayBackedIntervalTree<E>
where
    E: EntryT,
    E::N: Default,
{
    fn from_iter<T: IntoIterator<Item = E>>(iter: T) -> Self {
        let mut tree = Self::new();
        iter.into_iter()
            .for_each(|entry| tree.insert(entry));
        tree.index();
        tree
    }
}

/// Iterator over the reference of the tree
pub struct ArrayBackedIntervalTreeIter<'a, E>
where
    E: 'a,
    E: EntryT,
    E::N: Default,
{
    abit: &'a ArrayBackedIntervalTree<E>,
    i: usize,
}

// Implement Iterator for ArrayBackedIntervalTreeIter
impl<'a, E> Iterator for ArrayBackedIntervalTreeIter<'a, E>
where
    E: EntryT,
    E::N: Default,
{
    type Item = &'a E;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i >= self.abit.entries.len() {
            None
        } else {
            let item = &self.abit.entries[self.i];
            self.i += 1;
            Some(&item.data)
        }
    }
}

// Implement IntoIterator for ArrayBackedIntervalTree
impl<'a, E> IntoIterator for &'a ArrayBackedIntervalTree<E>
where
    E: EntryT,
    E::N: Default,
{
    type Item = &'a E;
    type IntoIter = ArrayBackedIntervalTreeIter<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        ArrayBackedIntervalTreeIter {
            abit: self,
            i: 0,
        }
    }
}

fn max3<T: Ord>(a: T, b: T, c: T) -> T {
    a.max(b.max(c))
}


#[derive(Clone, Copy)]
struct StackCell {
    // node
    x: usize,
    // level
    k: usize,
    // false if left child hasn't been processed
    w: bool,
}

impl StackCell {
    fn empty() -> Self {
        Self {
            x: 0,
            k: 0,
            w: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Entry<N: Ord + Clone + Copy + std::fmt::Debug> {
    interval: Interval<N>,
    data: usize,
}

// Implement the EntryT trait for Entry
impl<N: Ord + Clone + Copy + std::fmt::Debug> EntryT for Entry<N> {
    type N = N;

    fn interval(&self) -> &Interval<N> {
        &self.interval
    }
}

impl<N: Ord + Clone + Copy + std::fmt::Debug> Entry<N> {
    pub fn new(interval: Interval<N>, data: usize) -> Self {
        Entry { interval, data }
    }
}

impl<'a, N: Ord + Clone + Copy + std::fmt::Debug> EntryT for &'a Entry<N> {
    type N = N;

    fn interval(&self) -> &Interval<N> {
        &self.interval
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;

    #[test]
    fn test_tree_of_references() {
        // create objects in vec and add reference to the tree
        let mut entries = Vec::new();
        entries.push(Entry::new((12..34).into(), 0));
        entries.push(Entry::new((0..23).into(), 1));
        entries.push(Entry::new((34..56).into(), 2));

        let mut tree: ArrayBackedIntervalTree<&Entry<i32>> = ArrayBackedIntervalTree::new();
        for entry in &entries {
            tree.insert(entry);
        }
        tree.index();
    }

    #[test]
    fn test_example() {
        let mut tree: ArrayBackedIntervalTree<Entry<i32>> = ArrayBackedIntervalTree::new();
        tree.insert(Entry::new(
            (12..34).into(),
            0,
        ));
        tree.insert(Entry::new(
            (0..23).into(),
            1,
        ));
        tree.insert(Entry::new(
            (34..56).into(),
            2,
        ));
        tree.index();
        let overlap = tree.find(22..25);

        let e1 = Entry::new(
            (0..23).into(),
            1,
        );
        let e2 = Entry::new(
            (12..34).into(),
            0,
        );
        let expected = vec![&e1, &e2];
        assert_eq!(overlap, expected);
    }

    /// Regression test: catch a scenario where the `max` value of an entry
    /// wasn't extended to take into account all of the leaf nodes it contained
    /// when indexing
    #[test]
    fn test_disjoint_two_element_search() {
        let mut tree: ArrayBackedIntervalTree<Entry<i32>> = ArrayBackedIntervalTree::new();
        tree.insert(Entry::new(
            (12..34).into(),
            0,
        ));
        tree.insert(Entry::new(
            (40..56).into(),
            1,
        ));
        tree.index();
        let overlap = tree.find(40..41);

        let e1 = Entry::new(
            (40..56).into(),
            1,
        );
        let expected = vec![&e1];
        assert_eq!(overlap, expected);
    }

    /// Test Eq and PartialEq implementations for Entry
    #[test]
    fn test_entry_eq() {
        let e1 = Entry::new(
            (0..23).into(),
            1,
        );
        let e2 = Entry::new(
            (0..23).into(),
            1,
        );
        assert_eq!(e1, e2);

        let e2 = Entry::new(
            (0..25).into(),
            1,
        );
        assert_ne!(e1, e2);
    }

//     /// Test iterator over the reference of the tree
//     /// (i.e. the tree itself is not moved)
//     /// adds all entries to a new tree and compares
    #[test]
    fn test_iter_over_tree() {
        let mut tree: ArrayBackedIntervalTree<Entry<i32>> = ArrayBackedIntervalTree::new();
        tree.insert(Entry::new(
            (12..34).into(),
            0,
        ));
        tree.insert(Entry::new(
            (0..23).into(),
            1,
        ));
        tree.insert(Entry::new(
            (34..56).into(),
            2,
        ));
        tree.index();

        let mut res_tree: ArrayBackedIntervalTree<Entry<i32>> = ArrayBackedIntervalTree::new();
        for entry in &tree {
            res_tree.insert(entry.clone());
        }
        res_tree.index();
        assert_eq!(tree, res_tree);
    }

    #[test]
    fn test_tree_size() {
        let mut tree: ArrayBackedIntervalTree<Entry<i32>> = ArrayBackedIntervalTree::new();
        tree.insert(Entry::new(
            (12..34).into(),
            0,
        ));
        tree.insert(Entry::new(
            (0..23).into(),
            1,
        ));
        tree.insert(Entry::new(
            (34..56).into(),
            2,
        ));

        assert_eq!(tree.len(), 3);
    }

    proptest! {
        /// Given a query interval in the format `(start, len)` and a sequence
        /// of intervals `(start, len)` to index, assert that
        /// `ArrayBackedIntervalTree::find` returns all the intervals which
        /// overlap the query.
        #[test]
        fn find_arbitrary(
            query in (0u32..1001, 0u32..1001),
            intervals in prop::collection::vec((0u32..1000, 0u32..1000), 0..1000)
        ) {
            let tree = ArrayBackedIntervalTree::from_iter(
                intervals
                    .into_iter()
                    .enumerate()
                    .map(|(i, (start, len))| Entry::new((start..start + len).into(), i)),
            );

            let (start, len) = query;
            let end = start + len;

            let expected: Vec<_> = tree
                .entries
                .iter()
                .filter_map(|internal| {
                    if internal.interval().start < end && start < internal.interval().end {
                        Some(&internal.data)
                    } else {
                        None
                    }
                })
                .collect();

            prop_assert_eq!(
                tree.find(start..end),
                expected,
                "{:?} in {:?}",
                start..end,
                tree.entries
            );
        }
    }
}
