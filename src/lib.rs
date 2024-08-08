mod ast;
mod eval;
pub mod parser;
mod string;

pub use eval::evaluate;

trait Wrap<T> {
    fn wrap<F, U>(self, f: F) -> U
    where
        F: Fn(T) -> U,
        Self: Sized;

    fn wrap_ok<E>(self) -> Result<Self, E>
    where
        Self: Sized,
    {
        Ok(self)
    }
}

impl<T> Wrap<T> for T {
    fn wrap<F, U>(self, f: F) -> U
    where
        F: Fn(T) -> U,
    {
        f(self)
    }
}
