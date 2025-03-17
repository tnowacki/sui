// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::fmt::{Debug, Display};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Regex<Lbl> {
    labels: Vec<Lbl>,
    ends_in_dot_star: bool,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl<Lbl> Regex<Lbl> {
    pub fn epsilon() -> Self {
        Self {
            labels: vec![],
            ends_in_dot_star: false,
        }
    }

    pub fn label(lbl: Lbl) -> Self {
        Self {
            labels: vec![lbl],
            ends_in_dot_star: false,
        }
    }

    pub fn dot_star() -> Self {
        Self {
            labels: vec![],
            ends_in_dot_star: true,
        }
    }

    pub fn is_epsilon(&self) -> bool {
        self.labels.is_empty() && !self.ends_in_dot_star
    }

    pub fn abstract_size(&self) -> usize {
        1 + self.labels.len() + (self.ends_in_dot_star as usize)
    }

    /// Path for public facing API
    pub fn pub_path(&self) -> (Vec<Lbl>, bool)
    where
        Lbl: Clone,
    {
        (self.labels.clone(), self.ends_in_dot_star)
    }

    pub fn extend(&self, ext: &Self) -> Self
    where
        Lbl: Clone,
    {
        let mut r = self.clone();
        if r.ends_in_dot_star {
            r
        } else {
            let Self {
                labels,
                ends_in_dot_star,
            } = ext;
            r.labels.extend(labels.clone());
            r.ends_in_dot_star = *ends_in_dot_star;
            r
        }
    }

    /// If self = pq, then remove_prefix(p) returns Some(q)
    pub fn remove_prefix(&self, p: &Self) -> Vec<Regex<Lbl>>
    where
        Lbl: Clone,
        Lbl: Eq,
    {
        let mut self_walk = self.walk();
        let mut p_walk = p.walk();

        let mut result = Vec::new();
        loop {
            match (p_walk.peek(), self_walk.peek()) {
                (WalkPeek::EmptySet, _) => {
                    return result;
                }
                (_p_peek, WalkPeek::EmptySet) => {
                    // if we reach the end of self and p is not empty, we can't match
                    // (unless p was dot star)
                    // result not empty ==> p was dot star
                    debug_assert!(result.is_empty() || matches!(_p_peek, WalkPeek::DotStar));
                    return result;
                }
                (WalkPeek::DotStar, _) if self.ends_in_dot_star => {
                    // This is an optimization for the case where we have a list of labels
                    // with a dot star. If this ends in dot star we will eventually add it to
                    // the result set, and `r | .*` is equivalent to `.*` so we don't need the
                    // partial paths
                    return vec![Self::dot_star()];
                }
                (WalkPeek::Label(_), WalkPeek::Epsilon) => {
                    // we have a label in p not in self, so we can't match
                    debug_assert!(result.is_empty());
                    return result;
                }
                (WalkPeek::Label(l1), WalkPeek::Label(l2)) => {
                    if l1 != l2 {
                        // we have a label in p not in self, so we can't match
                        debug_assert!(result.is_empty());
                        return result;
                    }
                }
                (_, WalkPeek::DotStar) => {
                    // must be empty or we would have hit the optimization
                    debug_assert!(result.is_empty());
                    result.push(Self::dot_star());
                    return result;
                }
                (WalkPeek::Epsilon | WalkPeek::DotStar, _) => {
                    // if epsilon, we have a match and add it to the result
                    // if we have a dot star,
                    // we can consider the possibility of epsilon and similarly add to the result
                    if let Some(rem) = self_walk.remaining() {
                        result.push(rem);
                    };
                }
            }
            p_walk.next();
            self_walk.next();
        }
    }

    fn walk(&self) -> Walk<Lbl> {
        if self.is_epsilon() {
            Walk::Epsilon
        } else {
            Walk::Regex {
                regex: self,
                idx: 0,
            }
        }
    }
}

enum Walk<'a, Lbl> {
    EmptySet,
    Epsilon,
    Regex { regex: &'a Regex<Lbl>, idx: usize },
}

enum WalkPeek<'a, Lbl> {
    EmptySet,
    Epsilon,
    Label(&'a Lbl),
    DotStar,
}

impl<Lbl> Walk<'_, Lbl> {
    fn peek(&self) -> WalkPeek<'_, Lbl> {
        match self {
            Walk::EmptySet => WalkPeek::EmptySet,
            Walk::Epsilon => WalkPeek::Epsilon,
            Walk::Regex { regex, idx } => {
                if *idx < regex.labels.len() {
                    WalkPeek::Label(&regex.labels[*idx])
                } else if regex.ends_in_dot_star {
                    WalkPeek::DotStar
                } else {
                    debug_assert!(false);
                    WalkPeek::Epsilon
                }
            }
        }
    }

    fn next(&mut self) {
        match self {
            Walk::EmptySet => {}
            Walk::Epsilon => {
                *self = Walk::EmptySet;
            }
            Walk::Regex { regex, idx } => {
                if *idx < regex.labels.len() {
                    *idx += 1;
                } else if !regex.ends_in_dot_star {
                    // out of labels and not in dot star
                    // TODO should this be EmptySet or Epsilon?
                    *self = Walk::Epsilon;
                }
            }
        }
    }

    fn remaining(&self) -> Option<Regex<Lbl>>
    where
        Lbl: Clone,
    {
        match self {
            Walk::EmptySet => None,
            Walk::Epsilon => Some(Regex::epsilon()),
            Walk::Regex { regex, idx } => {
                let idx = *idx;
                let labels = if idx < regex.labels.len() {
                    regex.labels[idx..].to_vec()
                } else {
                    vec![]
                };
                let ends_in_dot_star = regex.ends_in_dot_star;
                Some(Regex {
                    labels,
                    ends_in_dot_star,
                })
            }
        }
    }
}

//**************************************************************************************************
// traits
//**************************************************************************************************

macro_rules! fmt_regex {
    ($f:expr, $path:expr) => {{
        let f = $f;
        let p = $path;
        let mut exts = p.labels.iter().peekable();
        while let Some(ext) = exts.peek() {
            // display the element
            ext.fmt(f)?;
            // advance the iterator
            exts.next();
            // if there is a next element, add a separator
            if exts.peek().is_some() {
                write!(f, ".")?;
            }
        }
        if p.ends_in_dot_star {
            write!(f, "_*")?;
        }
        Ok(())
    }};
}

impl<Lbl> Display for Regex<Lbl>
where
    Lbl: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_regex!(f, self)
    }
}

impl<Lbl> Debug for Regex<Lbl>
where
    Lbl: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_regex!(f, self)
    }
}
