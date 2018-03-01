# ct-wasm

This repository, forked from the [WebAssembly
Spec](https://github.com/WebAssembly/spec), contains additions to the
reference interpreter that allow for the encoding of constant-time
computations suitable for crypto.

NOTE: As a reference implementation, no guarantees are provided about the
execution timing of the extensions.

Conforming implementations must ensure that all operations on the s32 and s64
types be implemented in constant time. Otherwise, the typing rules here
presented will ensure the constant timedness of all programs over secrets.

## Summary of changes

### New Types
 - `s32`: Secret 32 bit integer
 - `s64`: Secret 64 bit integer

These types come with all integer operations except `div` and `rem` which are
notoriously non-CT and can leak information through partiality.

### New Memory
Each module is now allowed one `secret` memory alongside its 0 or 1 public memories.
They are declared in text as:
`(memory secret 0 10)`

Secret memories accept and produce secret values but require public indices for stores and loads.

To prepopulate a secret memory, use data segments as before but it is now important to utilize the
memory index option on data:

```lisp
(module
    (memory $sec secret 1)
    (memory $pub 1)

    (data $sec "Secret values")
    (data $pub "Public values"))
```

### Declassification
Declassification allows the relabeling of secret data as public. This is inherently unsound but important to operations such as encryption which produce a safely public value out of a secret one.

This is performed by the two operators:
 - `s32.declassify`
 - `s64.declassify`

These operators are only allowed inside **trusted functions**. By default, functions are untrusted.
Trust is built into the type of a function like so:

```lisp
(func trusted (param s32) (result i32)
    (s32.declassify (get_local 0)))
```