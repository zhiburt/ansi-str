# ansi-str [![Build Status](https://github.com/zhiburt/ansi-str/actions/workflows/ci.yml/badge.svg?style=for-the-badge)](https://github.com/zhiburt/ansi-str/actions) [![codecov](https://codecov.io/gh/zhiburt/ansi-str/branch/master/graph/badge.svg?token=8VGEM3ZT1T)](https://codecov.io/gh/zhiburt/ansi-str) [![Crate](https://img.shields.io/crates/v/ansi-str)](https://crates.io/crates/ansi-str) [![docs.rs](https://img.shields.io/badge/docs.rs-ansi--str-66c2a5?&color=blue&logo=docs.rs)](https://docs.rs/ansi-str/*/ansi_str/)

This is a library provides a set of methods to work with strings escaped with ansi code sequences.

It's an agnostic library in regard to different color libraries.
Therefore it can be used with any library (e.g. [owo-colors](https://crates.io/crates/owo-colors), [nu-ansi-term](https://crates.io/crates/nu-ansi-term)).

## Usage

```rust
use ansi_str::AnsiStr;
use owo_colors::{colors::*, OwoColorize};

pub fn main() {
    let text = "When the night has come"
        .fg::<Red>()
        .bg::<Cyan>()
        .bold()
        .to_string();

    let cut = text.ansi_get(5..).expect("ansi_get mustn't fail");

    println!("{}", text);
    println!("{}", cut);
}
```

Running this code will result in the following output.

![image](https://user-images.githubusercontent.com/20165848/151773080-d588a474-f43c-47b3-a29d-a92f19554907.png)

##### [For more examples, you check out the `examples` directory](https://github.com/zhiburt/ansi-str/tree/master/examples).

### Note

The library has derivatived from [zhiburt/ansi-cut](https://github.com/zhiburt/ansi-cut)
