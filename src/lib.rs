use std::rc::Rc;

type Id = String;

#[derive(PartialEq, Eq, Clone, Debug)]
enum Expr {
    U(u8),
    Pi(Id, Box<Expr>, Box<Expr>),
    Lam(Id, Option<Box<Expr>>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Var(Id),
    Sub(Box<Expr>, Box<Expr>, Id),
}

impl Expr {
    fn equal(&self, other: &Self, ctx: &Ctx) -> Result<(), ()> {
        todo!()
    }

    fn check(&self, ty: &Expr, ctx: &Ctx) -> Result<(), ()> {
        match (self, ty) {
            (Self::U(i), Self::U(j)) if i < j => Ok(()),
            (Self::Pi(x, a, b), Self::U(_)) => {
                a.check(ty, ctx)?;
                b.check(ty, &Ctx::Ext(ctx, x, a))?;
                Ok(())
            }
            (Self::Lam(x, o, t), Self::Pi(x_, a, b)) => {
                if x != x_ {
                    return Err(());
                }

                if let Some(a_) = o {
                    a.equal(a_, ctx)?;
                }

                t.check(b, &Ctx::Ext(ctx, x, a))?;

                Ok(())
            }
            (Self::App(f, t), Self::Sub(b, t_, x)) => {
                t.equal(t_, ctx)?;

                let Self::Pi(x_, a, b_) = f.synthesize(ctx)? else {
                    return Err(());
                };

                if *x != x_ {
                    return Err(());
                }

                b.equal(&b_, ctx)?;

                f.check(&Self::Pi(x.into(), a, b.to_owned()), ctx)?;

                Ok(())
            }
            (Self::Var(x), a) => {
                let a_ = ctx.lookup(x).ok_or(())?;
                a.equal(a_, ctx)?;

                Ok(())
            }
            (Self::Sub(t, u, x), a) => t.check(a, &Ctx::Ext(ctx, x, &u.synthesize(ctx)?)),
            _ => Err(()),
        }
    }

    fn synthesize(&self, ctx: &Ctx) -> Result<Self, ()> {
        match self {
            Self::U(i) => Ok(Self::U(i + 1)),
            Self::Pi(x, a, b) => {
                let Self::U(i) = a.synthesize(ctx)? else {
                    return Err(());
                };

                let Self::U(j) = b.synthesize(&Ctx::Ext(ctx, x, a))? else {
                    return Err(());
                };

                Ok(Self::U(i.max(j)))
            }
            Self::Lam(x, Some(a), t) => Ok(Self::Pi(
                x.into(),
                a.to_owned(),
                t.synthesize(&Ctx::Ext(ctx, x, a))?.into(),
            )),
            Self::App(g, t) => {
                let Self::Pi(x, a, b) = g.synthesize(ctx)? else {
                    return Err(());
                };

                t.check(&a, ctx)?;

                Ok(Self::Sub(b, t.to_owned(), x))
            }
            Self::Var(x) => Ok(ctx.lookup(x).ok_or(())?.to_owned()),
            Self::Sub(t, u, x) => t.synthesize(&Ctx::Ext(ctx, x, &u.synthesize(ctx)?)),
            _ => Err(()),
        }
    }
}

enum Ctx<'a> {
    Empty,
    Ext(&'a Ctx<'a>, &'a str, &'a Expr),
}

impl<'a> Ctx<'a> {
    fn ext(&'a self, x: &'a str, a: &'a Expr) -> Result<Self, ()> {
        if self.lookup(x).is_some() {
            return Err(());
        }

        Ok(Self::Ext(self, x, a))
    }

    fn lookup(&self, x: &str) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::Ext(_, y, t) if x == *y => Some(t),
            Self::Ext(env, _, _) => env.lookup(x),
        }
    }
}

enum Env<'a> {
    Empty,
    Ext(&'a Env<'a>, &'a str, &'a Expr),
}

impl<'a> Env<'a> {
    fn lookup(&self, x: &str) -> Option<&Expr> {
        match self {
            Self::Empty => None,
            Self::Ext(_, y, t) if x == *y => Some(t),
            Self::Ext(env, _, _) => env.lookup(x),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn id() -> Result<(), ()> {
        let ctx = Ctx::Empty;

        let term = Expr::Lam(
            "A".into(),
            Some(Expr::U(0).into()),
            Expr::Lam(
                "a".into(),
                Some(Expr::Var("A".into()).into()),
                Expr::Var("a".into()).into(),
            )
            .into(),
        );

        let ty = term.synthesize(&ctx)?;

        assert_eq!(
            ty,
            Expr::Pi(
                "A".into(),
                Expr::U(0).into(),
                Expr::Pi(
                    "a".into(),
                    Expr::Var("A".into()).into(),
                    Expr::Var("A".into()).into(),
                )
                .into()
            )
        );

        Ok(())
    }

    #[test]
    fn pq() -> Result<(), ()> {
        let ctx = Ctx::Empty.ext("Void", &Expr::U(0))?;
        let ctx = ctx.ext("P", &Expr::U(0))?;
        let ctx = ctx.ext("Q", &Expr::U(0))?;

        let ty = Expr::Sub(
            Expr::Pi(
                "pq".into(),
                Expr::Pi(
                    "p".into(),
                    Expr::Var("P".into()).into(),
                    Expr::Var("Q".into()).into(),
                )
                .into(),
                Expr::Pi(
                    "nq".into(),
                    Expr::App(Expr::Var("Not".into()).into(), Expr::Var("Q".into()).into()).into(),
                    Expr::App(Expr::Var("Not".into()).into(), Expr::Var("P".into()).into()).into(),
                )
                .into(),
            )
            .into(),
            Expr::Lam(
                "A".into(),
                Some(Expr::U(0).into()),
                Expr::Pi(
                    "_".into(),
                    Expr::Var("A".into()).into(),
                    Expr::Var("Void".into()).into(),
                )
                .into(),
            )
            .into(),
            "Not".into(),
        );

        assert_eq!(ty.synthesize(&ctx)?, Expr::U(0));

        // let term = Expr::Sub(
        //     Expr::Lam("pq".into(), Expr::Pi("_", Expr::Var("P".into()).into(), Expr::Var("Q".into()).into()), Expr::Lam("nq", None, Expr::)).into(),
        //     Expr::Lam("A".into(), Expr::U(0), Expr::Pi("_", Expr::Var("A"), Expr::Var("Void"))).into(),
        //     "not".into(),
        // );

        Ok(())
    }
}
