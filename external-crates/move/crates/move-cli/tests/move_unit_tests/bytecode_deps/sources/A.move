module A::A {
    use B::Bar;
    use C::Foo;

    public fun foo(): u64 {
        Bar::foo() + Foo::bar()
    }

    #[test]
    fun foo_test() {
        Bar::foo() + Foo::bar();
    }
}
