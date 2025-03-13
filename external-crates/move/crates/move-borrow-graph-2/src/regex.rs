// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::fmt::{Debug, Display};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Extension<Lbl> {
    Alias,
    Label(Lbl),
    Star,
}

pub enum Factored<Lbl> {
    None,
    // The path is a prefix of the given path
    Suffix(Path<Lbl>),
    // If the path starts with star, then the path is a prefix of the given path but! factoring
    // it out causes the star to remain
    Star,
}

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
    pub fn remove_prefix(&self, p: &Self) -> Option<Regex<Lbl>>
    where
        Lbl: Clone,
        Lbl: Eq,
    {
        let mut self_walk = self.walk();
        let mut p_walk = p.walk();
        if !p_walk.peek().matches(self_walk.peek()) {
            return None;
        }
        loop {
            if self_walk.in_dot_star() && p_walk.in_dot_star() {
                break Some(self_walk.remaining());
            }
            if p_walk.in_dot_star() {
                todo!("Not sure what to do in this case")
            }
            if p_walk.peek().matches(self_walk.peek()) {
                p_walk.next();
                self_walk.next();
            } else {
                break Some(self_walk.remaining());
            }
        }
    }

    fn walk(&self) -> Walk<Lbl> {
        Walk {
            regex: self,
            idx: 0,
        }
    }
}

struct Walk<'a, Lbl> {
    regex: &'a Regex<Lbl>,
    idx: usize,
}

enum WalkPeek<'a, Lbl> {
    Label(&'a Lbl),
    DotStar,
    Epsilon,
}

impl<Lbl> Walk<'_, Lbl> {
    fn peek(&self) -> WalkPeek<'_, Lbl> {
        if self.idx < self.regex.labels.len() {
            WalkPeek::Label(&self.regex.labels[self.idx])
        } else if self.regex.ends_in_dot_star {
            WalkPeek::DotStar
        } else {
            WalkPeek::Epsilon
        }
    }

    fn next(&mut self) {
        if self.idx < self.regex.labels.len() {
            self.idx += 1;
        }
    }

    fn in_dot_star(&self) -> bool {
        self.idx >= self.regex.labels.len() && self.regex.ends_in_dot_star
    }

    fn remaining(&self) -> Regex<Lbl>
    where
        Lbl: Clone,
    {
        let labels = if self.idx < self.regex.labels.len() {
            self.regex.labels[self.idx..].to_vec()
        } else {
            vec![]
        };
        let ends_in_dot_star = self.regex.ends_in_dot_star;
        Regex {
            labels,
            ends_in_dot_star,
        }
    }
}

impl<Lbl> WalkPeek<'_, Lbl> {
    fn matches(self, other: WalkPeek<'_, Lbl>) -> bool
    where
        Lbl: Eq,
    {
        match (self, other) {
            (WalkPeek::DotStar, _) => true,
            (WalkPeek::Label(l1), WalkPeek::Label(l2)) => l1 == l2,
            (WalkPeek::Epsilon, WalkPeek::Epsilon) => true,
            (WalkPeek::Label(_), WalkPeek::DotStar) => false,
            (WalkPeek::Epsilon, WalkPeek::DotStar) => false,
            (WalkPeek::Label(_), WalkPeek::Epsilon) => false,
            (WalkPeek::Epsilon, WalkPeek::Label(_)) => false,
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
        let mut exts = p.regex.iter().peekable();
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
        if p.ends_in_star {
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
