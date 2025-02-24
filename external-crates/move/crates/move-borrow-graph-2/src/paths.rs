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
pub struct Path<Lbl> {
    path: Vec<Lbl>,
    ends_in_star: bool,
}

//**************************************************************************************************
// impls
//**************************************************************************************************

impl<Lbl> Path<Lbl> {
    pub fn empty() -> Self {
        Self {
            path: vec![],
            ends_in_star: false,
        }
    }

    pub fn extend_by_label(&mut self, lbl: Lbl) {
        self.path.push(lbl);
    }

    pub fn extend_by_star(&mut self) {
        self.ends_in_star = true;
    }

    // TODO have to factor for epsilon too or do I?
    pub fn factor_by_label(&self, lbl: Lbl) -> Factored<Lbl> {
        match (self.path.first(), self.ends_in_star) {
            (None, false) => Factored::None,
            (None, true) => Factored::Star,
            (Some(first), _) if first == &lbl => Factored::Suffix(Path {
                path: self.path[1..].to_vec(),
                ends_in_star: self.ends_in_star,
            }),
            (Some(_), _) => Factored::None,
        }
    }
}

//**************************************************************************************************
// traits
//**************************************************************************************************

macro_rules! fmt_path {
    ($f:expr, $path:expr) => {{
        let f = $f;
        let p = $path;
        let mut exts = p.path.iter().peekable();
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
            write!(f, "*")?;
        }
        Ok(())
    }};
}

impl<Lbl> Display for Path<Lbl>
where
    Lbl: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_path!(f, self)
    }
}

impl<Lbl> Debug for Path<Lbl>
where
    Lbl: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_path!(f, self)
    }
}
