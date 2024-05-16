# cargo-pinch

~~Rust memory safety &amp; undefined behavior detector aimed at FFI usages.~~

Pinch is an Contract Violation detection tool for Rust crates. It can analyze libraries to detect unsafe code that fails to uphold its safety requirements. For instance:

- Obtaining `&mut T` out of `Pin<Box<T>>`, where `T: !Unpin`
- ...

## Using Pinch

Install Python dependencies:

```sh
pip install -r requirements.txt
```

Next, encode the Rust crate to be analyzed. This part is currently manual but will be automated. To encode, edit `pinch.py`:

1. Encode function signatures in `fn_tmps`, e.g.,
    - Original: `fn deref_mut<T>(_: MoveRef<T>) -> &mut T;`
    - Encoded: `"deref_mut": (1, lambda t1: (("MoveRef", t1), ("MutRef", t1))),`
2. Encode the detection goal in the `reachable` variable, e.g.,
    - Goal: Is `&mut Unmovable` obtainable from `Pin<Box<Unmovable>>`?
    - Encoded: `solver.reachable(ty_from=("Pin", ("Box", "Unmovable")), ty_to=("MutRef", "Unmovable"))`

Now you can run `pinch.py`:

```sh
python pinch.py
```

You will get `True` if obtainable, and `False` otherwise.
