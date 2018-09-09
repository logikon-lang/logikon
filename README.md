# Logikon

Logikon's compiler is written in Rust.  It compiles to YUL, the low-level
intermediate representation used in Solidity, which can be compiled to
multiple bytecode versions.

## Build

Compile for emscripten with (make sure emscripten's `emcc` is installed):
```bash
cargo build --target=asmjs-unknown-emscripten --release
```

## Language Design

https://github.com/logikon-lang/design
